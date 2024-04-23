import sys, os
import argparse
from openai import OpenAI
import gradio as gr
import time
import random
import json

from tutor.query_openai import get_gpt4_response, get_client
from tutor.check_formal_proof import get_formal_checker_response


def get_few_shot(stage, proof_strategy, num_examples):
    with open('theorems/example/proof_bank.json') as f:
        proof_bank = json.load(f)

    examples = []
    few_shot = []

    proof_strategies = ["Contradiction", "Contrapositive", "Direct", "Induction", "Witness"]

    if not proof_strategy or proof_strategy == "Other":
        for _ in range(num_examples):
            random_strategy = random.choice(proof_strategies)
            examples.append(random.choice(proof_bank[random_strategy][stage]))
    else:
        examples = random.sample(proof_bank[proof_strategy][stage], num_examples)
    for example in examples:
        user = example["user"]
        assistant = example["assistant"]
        few_shot.append({"role": "user", "content": user})
        few_shot.append({"role": "assistant", "content": assistant})
    return few_shot
        
def get_system_message(stage):
    match stage:
        case "Stage 1":
            return {"role": "system", "content": "You are a tutor for an introductory math proof writing class. You are helping a student who does not understand the problem they are working on. Do not give any part of the proof.\n"}
        case "Stage 2":
            return {"role": "system", "content": "You are a tutor for an introductory math proof writing class. You are helping a student who understands the problem they are working on, but does not know how to begin writing the proof. Suggest which methods of proof may be successful for the problem. Do not give away any part of the proof.\n"}
        case "Stage 3":
            return {"role": "system", "content": "You are a tutor for an introductory math proof writing class. You are helping a student who has begun writing a proof for the problem statement but doesn’t know how to proceed to a finished proof. Verify whether or not the student is on the right track. If they are on the right track, give a hint for the next step. If they are not on the right track, identify what they did wrong. Do not give away any parts of the correct proof.\n"}
        case "Stage 4":
            return {"role": "system", "content": "You are a tutor for an introductory math proof writing class. You are helping a student who completed a proof for the problem statement and wants to verify the correctness of their proof. Do not give any part of the proof.\n"}
        case _:
            return {"role": "system", "content": "You are a tutor for an introductory math proof writing class. You are helping a student who can be in any stage of the proof writing process. Do not give any part of the proof.\n"}

def get_tutor_response(user_message, chat_history, proof_statement, stage, proof_strategy):
    conversation = []

    # system message
    conversation.append(get_system_message(stage[0:7]))

    # initial query (few-shot)
    if chat_history == []:
        # num_examples = 1
        # few_shot = get_few_shot(stage[0:7], proof_strategy, num_examples)
        # for message in few_shot:
        #     conversation.append(message)
        conversation.append({"role": "user", "content": f"Proof Statement:\n{proof_statement}\n{user_message}\n"})
    # continued conversation
    else:
        # chat_history: (user, assistant) tuples.
        for message in chat_history:
            conversation.append({"role": "user", "content": message[0]})
            conversation.append({"role": "assistant", "content": message[1]})
        conversation.append({"role": "user", "content": user_message})
    
    # get gpt informal result
    temperature = 0
    model_name = "gpt-4"
    bot_message = get_gpt4_response(
        conversation,
        temperature,
        model_name
    )

    # target stage 4 correctness
    if stage[0:7] == "Stage 4":
        # informal correctness
        temperature = 0
        model_name = "gpt-4"
        informal_correct = bool(get_gpt4_response(
            [{"role": "user", "content": f"Tell me True if your response indicates the proof is correct, False if your response indicates the proof is incorrect.\nThis was your response:\n{bot_message}"}],
            temperature,
            model_name
        ))
        print(informal_correct)
        # formal correctness
        formal_correct = get_formal_checker_response(user_message, proof_statement)
        print(formal_correct)

        # 4 cases of informal/formal
        match informal_correct, formal_correct:
            # case 1: informal correct / formal correct
            case True, True:
                print("informal correct / formal correct, do nothing")
            # case 2: informal correct / formal incorrect
            case True, False:
                print("informal correct / formal incorrect")
                conversation.pop()
                # feed back to GPT-4, say formalized attempt is incorrect
                conversation.append(({"role": "user", "content": f"Proof Statement:\n{proof_statement}\nMy proof attempt is incorrect when I formalized it into formal proof with Lean 4.\nMy Attempt:\n{user_message}\n"}))
                bot_message = get_gpt4_response(
                    conversation,
                    temperature,
                    model_name
                )
            # case 3: informal incorrect / formal correct
            case False, True:
                print("informal incorrect / formal correct")
                conversation.pop()
                # feed back to GPT-4, say formalized attempt is correct
                conversation.append(({"role": "user", "content": f"Proof Statement:\n{proof_statement}\nMy proof attempt is correct when I formalized it into formal proof with Lean 4.\nMy Attempt:\n{user_message}\n"}))
                bot_message = get_gpt4_response(
                    conversation,
                    temperature,
                    model_name
                )
            # case 4: informal incorrect / formal incorrect
            case False, False:
                print("informal incorrect / formal incorrect, correctly found mistakes, do nothing")
            case _, _:
                print("error")

    chat_history.append((user_message, bot_message))
    print(chat_history)
    time.sleep(1)
    return "", chat_history


if __name__ == "__main__":
    with gr.Blocks() as tutor:
        with gr.Row():
            proof_statement = gr.Dropdown(["OddSumEven", "Other"], allow_custom_value = True, label="Proof Statement", info="Which proof would you like assistance on?")
            stage = gr.Dropdown(["Stage 1: I don't understand the problem.", "Stage 2: I don't know how to begin.", "Stage 3: I don't know how to proceed.", "Stage 4: I completed the proof."], label="Stage", info="What stage of the proof writing process are you on?")        
            proof_strategy = gr.Dropdown(["Contradiction", "Contrapositive", "Direct", "Induction", "Witness", "Other"], label="Proof Strategy - Optional", info="Do you know which proof strategy to use?")        
        with gr.Row():
            with gr.Column(scale = 1):
                message = gr.Textbox(label = "Message", lines = 13)
                submit = gr.Button("Send")
            with gr.Column(scale = 2):
                chatbot = gr.Chatbot(show_copy_button = True, height = 345)
                clear = gr.ClearButton([message, chatbot])
        submit.click(get_tutor_response, [message, chatbot, proof_statement, stage, proof_strategy], [message, chatbot])

    tutor.launch(share=True)
    