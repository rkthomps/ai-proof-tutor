import sys, os
import argparse
from openai import OpenAI
import gradio as gr
import time

from tutor.query_openai import get_gpt4_response, get_client


# def read_file(file_path: str) -> str:
#     with open(file_path, "r") as fin:
#         return fin.read()

# accessing dictionary: proof_bank[stage#][example#] -> returns 1D list of user + assistant pair
proof_bank = [
    [
        [{"role": "user", "content": f"I am working on proving the statement:\nproblem_placeholder\nI don't understand the problem.\n"}, 
         {"role": "assistant", "content": "response_placeholder"}],
        [{"role": "user", "content": f"I am working on proving the statement:\nproblem_placeholder\nI don't understand the problem.\n"}, 
         {"role": "assistant", "content": "response_placeholder"}]
    ],
    [
        [{"role": "user", "content": f"I am working on proving the statement:\nproblem_placeholder\nI don't know how to begin the proof.\n"}, 
         {"role": "assistant", "content": "response_placeholder"}],
        [{"role": "user", "content": f"I am working on proving the statement:\nproblem_placeholder\nI don't know how to begin the proof.\n"}, 
         {"role": "assistant", "content": "response_placeholder"}]
    ],
    [
        [{"role": "user", "content": f"I am working on proving the statement:\nproblem_placeholder\nThis is what I have so far:\nattempt_placeholder\n"}, 
         {"role": "assistant", "content": "response_placeholder"}],
        [{"role": "user", "content": f"I am working on proving the statement:\nproblem_placeholder\nThis is what I have so far:\nattempt_placeholder\n"}, 
         {"role": "assistant", "content": "response_placeholder"}]
    ],
    [
        [{"role": "user", "content": f"I am working on proving the statement:\nproblem_placeholder\nPlease verify the correctness of my proof:\nattempt_placeholder\n"}, 
         {"role": "assistant", "content": "response_placeholder"}],
        [{"role": "user", "content": f"I am working on proving the statement:\nproblem_placeholder\nPlease verify the correctness of my proof:\nattempt_placeholder\n"}, 
         {"role": "assistant", "content": "response_placeholder"}]
    ]
]

def get_conversation(stage):
    conversation = []
    match stage:
        case "Stage 1":
            conversation = [{"role": "system", "content": "You are a tutor for an introductory math proof writing class. You are helping a student who does not understand the problem they are working on. Do not give any part of the proof.\n"}]
            return conversation + proof_bank[0][0] + proof_bank[0][1]
        case "Stage 2":
            conversation = [{"role": "system", "content": "You are a tutor for an introductory math proof writing class. You are helping a student who understands the problem they are working on, but does not know how to begin writing the proof. Suggest which methods of proof may be successful for the problem. Do not give away any part of the proof.\n"}]
            return conversation + proof_bank[1][0] + proof_bank[1][1]
        case "Stage 3":
            conversation = [{"role": "system", "content": "You are a tutor for an introductory math proof writing class. You are helping a student who has begun writing a proof for the problem statement but doesn’t know how to proceed to a finished proof. Verify whether or not the student is on the right track. If they are on the right track, give a hint for the next step. If they are not on the right track, identify what they did wrong. Do not give away any parts of the correct proof.\n"}]
            return conversation + proof_bank[2][0] + proof_bank[2][1]
        case "Stage 4":
            conversation = [{"role": "system", "content": "You are a tutor for an introductory math proof writing class. You are helping a student who completed a proof for the problem statement and wants to verify the correctness of their proof. Do not give any part of the proof.\n"}]
            return conversation + proof_bank[3][0] + proof_bank[3][1]

# def get_few_shot_examples(proof_strategy):
#     match proof_strategy:
#         case "Contradiction":
#             return
#         case "Witness":
#             return
#         case "Induction":
#             return
#         case "Other":
#             return

def get_tutor_response(user_message, chat_history, proof, stage):
    conversation = []
    # initial query (few shot)
    if chat_history == []:
        conversation = get_conversation(stage[0:7])
        conversation.append({"role": "user", "content": f"I am working on proving the statement:\n{proof}\n{user_message}\n"})
    # continued conversation
    else:
        # chat_history: (user, assistant) tuples.
        for message in chat_history:
            conversation.append({"role": "user", "content": message[0]})
            conversation.append({"role": "assistant", "content": message[1]})
        conversation.append({"role": "user", "content": user_message})
    temperature = 0
    model_name = "gpt-4"
    bot_message = get_gpt4_response(
        conversation,
        temperature,
        model_name
    )
    chat_history.append((user_message, bot_message))
    time.sleep(1)
    return "", chat_history


# def format_response(
#     theorem_statement: str, proof_attempt: str, ground_truth_proof: str, response: str
# ) -> str:
#     return (
#         f"Theorem Statement:\n{theorem_statement}\n\n"
#         f"Correct Proof:\n{ground_truth_proof}\n\n"
#         f"Proof Attempt:\n{proof_attempt}\n\n"
#         f"Response:\n{response}"
#     )


if __name__ == "__main__":
    # COMMAND LINE TOOL VERSION
    # parser = argparse.ArgumentParser(
    #     "Command line interface (CLI) for CSE 20 AI Tutor."
    # )
    # parser.add_argument(
    #     "theorem_statement_path", help="Path to file with theorem statement."
    # )
    # parser.add_argument(
    #     "proof_attempt_path", help="Path to file with student proof attempt."
    # )
    # parser.add_argument(
    #     "ground_truth_proof_path", help="Path to file with ground truth proof."
    # )
    # parser.add_argument(
    #     "method", help="Experiment method."
    # )
    # parser.add_argument(
    #     "stage", help="Stage in proccess of studen't proof."
    # )
    # args = parser.parse_args(sys.argv[1:])

    # # system_message = read_file("theorems/example/system_message.txt")
    # theorem_statement = read_file(args.theorem_statement_path)
    # proof_attempt = read_file(args.proof_attempt_path)
    # ground_truth_proof = read_file(args.ground_truth_proof_path)
    # method = args.method
    # stage = args.stage
    # client = get_client()

    # response = get_tutor_response(
    #     method, stage, theorem_statement, proof_attempt, ground_truth_proof, client
    # )
    # print(
    #     format_response(theorem_statement, proof_attempt, ground_truth_proof, response)
    # )


    # SINGLE ROUND VERSION
    # demo = gr.Interface(
    #     fn=get_tutor_response,
    #     inputs=[gr.Dropdown(
    #             ["Contradiction", "Witness", "Induction", "Other"], label="Proof", info="Which proof would you like assistance on?"
    #         ),
    #             gr.Dropdown(
    #             ["Stage 1: I don't understand the problem.", "Stage 2: I don't know how to begin.", "Stage 3: I don't know how to proceed.", "Stage 4: I completed the proof."], label="Stage", info="What stage of the proof writing process are you on?"
    #         ),
    #             "text"],
    #     outputs=["text"],
    # )


    # MULTIROUND CHATBOT VERSION
    with gr.Blocks() as demo:
        proof = gr.Dropdown(["Contradiction", "Witness", "Induction", "Other"], label="Proof", info="Which proof would you like assistance on?")        
        stage = gr.Dropdown(["Stage 1: I don't understand the problem.", "Stage 2: I don't know how to begin.", "Stage 3: I don't know how to proceed.", "Stage 4: I completed the proof."], label="Stage", info="What stage of the proof writing process are you on?")        
        chatbot = gr.Chatbot()
        message = gr.Textbox()
        clear = gr.ClearButton([message, chatbot])

        # def respond(message, chat_history, problem, step):
        #     bot_message = "Helping with " + problem + " on " + step
        #     chat_history.append((message, bot_message))
        #     time.sleep(1)
        #     return "", chat_history

        message.submit(get_tutor_response, [message, chatbot, proof, stage], [message, chatbot])

    demo.launch(share=True)