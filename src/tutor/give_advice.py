import sys, os
import argparse
from openai import OpenAI
import gradio as gr
import time
import random
import json

from tutor.query_openai import get_gpt4_response, get_client
from tutor.check_formal_proof import get_formal_checker_response


def get_few_shot(stage, num_examples):
    conversation = []

    with open('theorems/example/fewshot_bank.json') as f:
        fewshot_bank = json.load(f)
    few_shot = random.sample(fewshot_bank[stage], num_examples)
    
    for example in few_shot:
        proof = example["proof"]
        user = example["user"]
        assistant = example["assistant"]
        conversation.append({"role": "user", "content": f"Proof Statement:\n{proof}\n\n{user}"})
        conversation.append({"role": "assistant", "content": assistant})
    return conversation
        
def get_system_message(stage):
    match stage:
        case "Stage 1":
            return {"role": "system", "content": "You are a tutor for an introductory math proof writing class. You are helping a student who does not understand the problem they are working on. Do not give any part of the proof.\n"}
        case "Stage 2":
            return {"role": "system", "content": "You are a tutor for an introductory math proof writing class. You are helping a student who understands the problem they are working on, but does not know how to begin writing the proof. Suggest which methods of proof may be successful for the problem. Do not give away any part of the proof.\n"}
        case "Stage 3":
            return {"role": "system", "content": "You are a tutor for an introductory math proof writing class. You are helping a student who has begun writing a proof for the problem statement but does not know how to proceed to a finished proof. Verify whether or not the student is on the right track. If they are on the right track, give a hint for the next step. If they are not on the right track, identify what they did wrong. Do not give away any parts of the correct proof.\n"}
        case "Stage 4":
            return {"role": "system", "content": "You are a tutor for an introductory math proof writing class. You are helping a student who completed a proof for the problem statement and wants to verify the correctness of their proof. Do not give any part of the proof.\n"}
        case _:
            return {"role": "system", "content": "You are a tutor for an introductory math proof writing class. You are helping a student who can be in any stage of the proof writing process. Do not give any part of the proof.\n"}

def get_tutor_response(user_message, chat_history, proof_statement, custom_proof, stage):
    if (proof_statement == "Other"):
        proof_statement = custom_proof

    conversation = []

    # system message
    conversation.append(get_system_message(stage[0:7]))

    # initial query (few-shot)
    if chat_history == []:
        num_examples = 2
        few_shot = get_few_shot(stage[0:7], num_examples)
        for message in few_shot:
            conversation.append(message)
    # continued conversation
    else:
        # chat_history: (user, assistant) tuples.
        for message in chat_history:
            conversation.append({"role": "user", "content": message[0]})
            conversation.append({"role": "assistant", "content": message[1]})
            
    conversation.append({"role": "user", "content": f"Proof Statement:\n{proof_statement}\n\n{user_message}"})
    
    # get gpt informal result
    temperature = 0
    model_name = "gpt-4"
    gpt_message = get_gpt4_response(
        conversation,
        temperature,
        model_name
    )

    # target stage 4 correctness
    with open('theorems/example/proof_bank.json') as f:
        proof_bank = json.load(f)
    if (stage[0:7] == "Stage 4" and proof_statement in proof_bank):
        formal_correct = get_formal_checker_response(user_message, proof_bank[proof_statement])
        if (formal_correct):
            gpt_message += "\n\n(Formalized Proof Attempt Passed \u2705)"
        else:
            gpt_message += "\n\n(Formalized Proof Attempt Failed \u274C)"

    chat_history.append((user_message, gpt_message))
    time.sleep(1)
    return "", chat_history


if __name__ == "__main__":
    def get_statements():
        with open('theorems/example/proof_bank.json') as f:
            proof_bank = json.load(f)
        return list(proof_bank.keys())

    def enable_submit_button(statement, custom, stage, message):
        if (statement != [] and stage != [] and message != ""):
            if (statement == "Other" and custom == ""):
                return gr.Button(interactive = False)
            else:
                return gr.Button(interactive = True)
        else:
            return gr.Button(interactive = False)
        
    def enable_clear_button(chatbot):
        if (chatbot != []):
            return gr.ClearButton(interactive = True)
        else:
            return gr.ClearButton(interactive = False)
    
    with gr.Blocks() as tutor:
        with gr.Row():
            with gr.Column(scale = 1):
                with gr.Group():
                    with gr.Row():
                        proof_statement = gr.Dropdown(get_statements() + ["Other"], label="Proof Statement", info="Which proof would you like assistance on?", allow_custom_value=True)
                    with gr.Row():
                        custom_proof = gr.Textbox(label = "Proof Statement (Other)", info = "Input your proof statment here if you selected \"Other\".", lines = 10)
                    with gr.Row():
                        stage = gr.Dropdown(["Stage 1: I don't understand the problem.", "Stage 2: I don't know how to begin.", "Stage 3: I don't know how to proceed.", "Stage 4: I completed the proof."], label="Stage", info="What stage of the proof writing process are you on?")        
            with gr.Column(scale = 2):
                with gr.Group():
                    chatbot = gr.Chatbot(show_copy_button = True, height = 400)
                    message = gr.Textbox(label = "Message", lines = 2)
                with gr.Row():
                    clear = gr.ClearButton([message, chatbot], value = "Clear Chat", interactive = False)
                    submit = gr.Button(value = "Send", scale = 3, interactive = False)
        proof_statement.change(enable_submit_button, [proof_statement, custom_proof, stage, message], submit)
        custom_proof.change(enable_submit_button, [proof_statement, custom_proof, stage, message], submit)
        stage.change(enable_submit_button, [proof_statement, custom_proof, stage, message], submit)
        message.change(enable_submit_button, [proof_statement, custom_proof, stage, message], submit)
        chatbot.change(enable_clear_button, chatbot, clear)
        submit.click(get_tutor_response, [message, chatbot, proof_statement, custom_proof, stage], [message, chatbot])

    tutor.launch(share=True)
    