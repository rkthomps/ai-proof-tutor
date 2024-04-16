import sys, os
import argparse
from openai import OpenAI
import gradio as gr
import time
import random

from tutor.query_openai import get_gpt4_response, get_client
from tutor.check_formal_proof import get_formal_checker_response


# accessing dictionary: proof_bank[stage#][example#] -> returns 1D list of user + assistant pair
proof_bank = [
    # Stage 1
    [
        # Contradiction
        [
            [{"role": "user", "content": f"I am working on proving the statement:\nThere does not exist a greatest integer.\nI don't understand the problem.\n"}, 
            {"role": "assistant", "content": "The problem statement is asking you to prove that there is not one integer that has a greater value than all other integers. An integer is a whole number, which doesn't have fractions."}],
            [{"role": "user", "content": f"I am working on proving the statement:\nRANDOM_PLACEHOLDER_2\nI don't understand the problem.\n"}, 
            {"role": "assistant", "content": "response_placeholder"}],
            [{"role": "user", "content": f"I am working on proving the statement:\nRANDOM_PLACEHOLDER_3\nI don't understand the problem.\n"}, 
            {"role": "assistant", "content": "response_placeholder"}],
            [{"role": "user", "content": f"I am working on proving the statement:\nRANDOM_PLACEHOLDER_4\nI don't understand the problem.\n"}, 
            {"role": "assistant", "content": "response_placeholder"}]
        ],
        # Contrapositive
        [
            [{"role": "user", "content": f"I am working on proving the statement:\nThere does not exist a greatest integer.\nI don't understand the problem.\n"}, 
            {"role": "assistant", "content": "The problem statement is asking you to prove that there is not one integer that has a greater value than all other integers. An integer is a whole number, which doesn't have fractions."}],
            [{"role": "user", "content": f"I am working on proving the statement:\nRANDOM_PLACEHOLDER_2\nI don't understand the problem.\n"}, 
            {"role": "assistant", "content": "response_placeholder"}],
            [{"role": "user", "content": f"I am working on proving the statement:\nRANDOM_PLACEHOLDER_3\nI don't understand the problem.\n"}, 
            {"role": "assistant", "content": "response_placeholder"}],
            [{"role": "user", "content": f"I am working on proving the statement:\nRANDOM_PLACEHOLDER_4\nI don't understand the problem.\n"}, 
            {"role": "assistant", "content": "response_placeholder"}]
        ],
        # Direct
        [
            [{"role": "user", "content": f"1I am working on proving the statement:\nThere does not exist a greatest integer.\nI don't understand the problem.\n"}, 
            {"role": "assistant", "content": "The problem statement is asking you to prove that there is not one integer that has a greater value than all other integers. An integer is a whole number, which doesn't have fractions."}],
            [{"role": "user", "content": f"2I am working on proving the statement:\nRANDOM_PLACEHOLDER_2\nI don't understand the problem.\n"}, 
            {"role": "assistant", "content": "response_placeholder"}],
            [{"role": "user", "content": f"3I am working on proving the statement:\nRANDOM_PLACEHOLDER_3\nI don't understand the problem.\n"}, 
            {"role": "assistant", "content": "response_placeholder"}],
            [{"role": "user", "content": f"4I am working on proving the statement:\nRANDOM_PLACEHOLDER_4\nI don't understand the problem.\n"}, 
            {"role": "assistant", "content": "response_placeholder"}]
        ],
        # Induction
        [
            [{"role": "user", "content": f"I am working on proving the statement:\nThere does not exist a greatest integer.\nI don't understand the problem.\n"}, 
            {"role": "assistant", "content": "The problem statement is asking you to prove that there is not one integer that has a greater value than all other integers. An integer is a whole number, which doesn't have fractions."}],
            [{"role": "user", "content": f"I am working on proving the statement:\nRANDOM_PLACEHOLDER_2\nI don't understand the problem.\n"}, 
            {"role": "assistant", "content": "response_placeholder"}],
            [{"role": "user", "content": f"I am working on proving the statement:\nRANDOM_PLACEHOLDER_3\nI don't understand the problem.\n"}, 
            {"role": "assistant", "content": "response_placeholder"}],
            [{"role": "user", "content": f"I am working on proving the statement:\nRANDOM_PLACEHOLDER_4\nI don't understand the problem.\n"}, 
            {"role": "assistant", "content": "response_placeholder"}]
        ],
        # Witness
        [
            [{"role": "user", "content": f"I am working on proving the statement:\nThere does not exist a greatest integer.\nI don't understand the problem.\n"}, 
            {"role": "assistant", "content": "The problem statement is asking you to prove that there is not one integer that has a greater value than all other integers. An integer is a whole number, which doesn't have fractions."}],
            [{"role": "user", "content": f"I am working on proving the statement:\nRANDOM_PLACEHOLDER_2\nI don't understand the problem.\n"}, 
            {"role": "assistant", "content": "response_placeholder"}],
            [{"role": "user", "content": f"I am working on proving the statement:\nRANDOM_PLACEHOLDER_3\nI don't understand the problem.\n"}, 
            {"role": "assistant", "content": "response_placeholder"}],
            [{"role": "user", "content": f"I am working on proving the statement:\nRANDOM_PLACEHOLDER_4\nI don't understand the problem.\n"}, 
            {"role": "assistant", "content": "response_placeholder"}]
        ]
    ],
    # Stage 2
    [
        # Contradiction
        [
            [{"role": "user", "content": f"I am working on proving the statement:\nThere does not exist a greatest integer.\nI don't know how to begin the proof.\n"}, 
            {"role": "assistant", "content": "This statement can be proved by universal generalization, meaning that you can use an arbitrary integer to show that it can never be the greatest integer."}],
            [{"role": "user", "content": f"I am working on proving the statement:\nproblem_placeholder\nI don't know how to begin the proof.\n"}, 
            {"role": "assistant", "content": "response_placeholder"}]
        ],
        # Contrapositive
        [
            [{"role": "user", "content": f"I am working on proving the statement:\nThere does not exist a greatest integer.\nI don't know how to begin the proof.\n"}, 
            {"role": "assistant", "content": "This statement can be proved by universal generalization, meaning that you can use an arbitrary integer to show that it can never be the greatest integer."}],
            [{"role": "user", "content": f"I am working on proving the statement:\nproblem_placeholder\nI don't know how to begin the proof.\n"}, 
            {"role": "assistant", "content": "response_placeholder"}]
        ],
        # Direct
        [
            [{"role": "user", "content": f"I am working on proving the statement:\nThere does not exist a greatest integer.\nI don't know how to begin the proof.\n"}, 
            {"role": "assistant", "content": "This statement can be proved by universal generalization, meaning that you can use an arbitrary integer to show that it can never be the greatest integer."}],
            [{"role": "user", "content": f"I am working on proving the statement:\nproblem_placeholder\nI don't know how to begin the proof.\n"}, 
            {"role": "assistant", "content": "response_placeholder"}]
        ],
        # Induction
        [
            [{"role": "user", "content": f"I am working on proving the statement:\nThere does not exist a greatest integer.\nI don't know how to begin the proof.\n"}, 
            {"role": "assistant", "content": "This statement can be proved by universal generalization, meaning that you can use an arbitrary integer to show that it can never be the greatest integer."}],
            [{"role": "user", "content": f"I am working on proving the statement:\nproblem_placeholder\nI don't know how to begin the proof.\n"}, 
            {"role": "assistant", "content": "response_placeholder"}]
        ],
        # Witness
        [
            [{"role": "user", "content": f"I am working on proving the statement:\nThere does not exist a greatest integer.\nI don't know how to begin the proof.\n"}, 
            {"role": "assistant", "content": "This statement can be proved by universal generalization, meaning that you can use an arbitrary integer to show that it can never be the greatest integer."}],
            [{"role": "user", "content": f"I am working on proving the statement:\nproblem_placeholder\nI don't know how to begin the proof.\n"}, 
            {"role": "assistant", "content": "response_placeholder"}]
        ]
    ],
    # Stage 3
    [
        # Contradiction
        [
            [{"role": "user", "content": f"I am working on proving the statement:\There does not exist a greatest integer.\nThis is what I have so far:\Let m be an arbitrary integer. Then n = m+1 is a witness. How do I continue the proof?\n"}, 
            {"role": "assistant", "content": "You are on the right track! The next step is to compare m and n to show how the witness n proves that there doesn't exist a greatest integer."}],
            [{"role": "user", "content": f"I am working on proving the statement:\nproblem_placeholder\nThis is what I have so far:\nattempt_placeholder\n"}, 
            {"role": "assistant", "content": "response_placeholder"}]
        ],
        # Contrapositive
        [
            [{"role": "user", "content": f"I am working on proving the statement:\There does not exist a greatest integer.\nThis is what I have so far:\Let m be an arbitrary integer. Then n = m+1 is a witness. How do I continue the proof?\n"}, 
            {"role": "assistant", "content": "You are on the right track! The next step is to compare m and n to show how the witness n proves that there doesn't exist a greatest integer."}],
            [{"role": "user", "content": f"I am working on proving the statement:\nproblem_placeholder\nThis is what I have so far:\nattempt_placeholder\n"}, 
            {"role": "assistant", "content": "response_placeholder"}]
        ],
        # Direct
        [
            [{"role": "user", "content": f"I am working on proving the statement:\There does not exist a greatest integer.\nThis is what I have so far:\Let m be an arbitrary integer. Then n = m+1 is a witness. How do I continue the proof?\n"}, 
            {"role": "assistant", "content": "You are on the right track! The next step is to compare m and n to show how the witness n proves that there doesn't exist a greatest integer."}],
            [{"role": "user", "content": f"I am working on proving the statement:\nproblem_placeholder\nThis is what I have so far:\nattempt_placeholder\n"}, 
            {"role": "assistant", "content": "response_placeholder"}]
        ],
        # Induction
        [
            [{"role": "user", "content": f"I am working on proving the statement:\There does not exist a greatest integer.\nThis is what I have so far:\Let m be an arbitrary integer. Then n = m+1 is a witness. How do I continue the proof?\n"}, 
            {"role": "assistant", "content": "You are on the right track! The next step is to compare m and n to show how the witness n proves that there doesn't exist a greatest integer."}],
            [{"role": "user", "content": f"I am working on proving the statement:\nproblem_placeholder\nThis is what I have so far:\nattempt_placeholder\n"}, 
            {"role": "assistant", "content": "response_placeholder"}]
        ],
        # Witness
        [
            [{"role": "user", "content": f"I am working on proving the statement:\There does not exist a greatest integer.\nThis is what I have so far:\Let m be an arbitrary integer. Then n = m+1 is a witness. How do I continue the proof?\n"}, 
            {"role": "assistant", "content": "You are on the right track! The next step is to compare m and n to show how the witness n proves that there doesn't exist a greatest integer."}],
            [{"role": "user", "content": f"I am working on proving the statement:\nproblem_placeholder\nThis is what I have so far:\nattempt_placeholder\n"}, 
            {"role": "assistant", "content": "response_placeholder"}]
        ]
    ],
    # Stage 4
    [
        # Contradiction
        [
            [{"role": "user", "content": f"I am working on proving the statement:\There does not exist a greatest integer.\nPlease verify the correctness of my proof:\Consider 1 trillion as a witness. This is a very large number, but 2 trillion is an even bigger number, so 1 trillion is not the greatest integer. Therefore, there isn't a greatest integer, as desired.\n"}, 
            {"role": "assistant", "content": "Your attempt unfortunately doesn't prove the statement: there does not exist a greatest integer. To correctly prove it, you want to show that the statement is true for any arbitrary integer, not just a single value, like 1 trillion. Try to generalize your proof so that it can correctly show that any integer is not the greatest integer."}],
            [{"role": "user", "content": f"I am working on proving the statement:\nproblem_placeholder\nPlease verify the correctness of my proof:\nattempt_placeholder\n"}, 
            {"role": "assistant", "content": "response_placeholder"}]
        ],
        # Contrapositive
        [
            [{"role": "user", "content": f"I am working on proving the statement:\There does not exist a greatest integer.\nPlease verify the correctness of my proof:\Consider 1 trillion as a witness. This is a very large number, but 2 trillion is an even bigger number, so 1 trillion is not the greatest integer. Therefore, there isn't a greatest integer, as desired.\n"}, 
            {"role": "assistant", "content": "Your attempt unfortunately doesn't prove the statement: there does not exist a greatest integer. To correctly prove it, you want to show that the statement is true for any arbitrary integer, not just a single value, like 1 trillion. Try to generalize your proof so that it can correctly show that any integer is not the greatest integer."}],
            [{"role": "user", "content": f"I am working on proving the statement:\nproblem_placeholder\nPlease verify the correctness of my proof:\nattempt_placeholder\n"}, 
            {"role": "assistant", "content": "response_placeholder"}]
        ],
        # Direct
        [
            [{"role": "user", "content": f"I am working on proving the statement:\There does not exist a greatest integer.\nPlease verify the correctness of my proof:\Consider 1 trillion as a witness. This is a very large number, but 2 trillion is an even bigger number, so 1 trillion is not the greatest integer. Therefore, there isn't a greatest integer, as desired.\n"}, 
            {"role": "assistant", "content": "Your attempt unfortunately doesn't prove the statement: there does not exist a greatest integer. To correctly prove it, you want to show that the statement is true for any arbitrary integer, not just a single value, like 1 trillion. Try to generalize your proof so that it can correctly show that any integer is not the greatest integer."}],
            [{"role": "user", "content": f"I am working on proving the statement:\nproblem_placeholder\nPlease verify the correctness of my proof:\nattempt_placeholder\n"}, 
            {"role": "assistant", "content": "response_placeholder"}]
        ],
        # Induction
        [
            [{"role": "user", "content": f"I am working on proving the statement:\There does not exist a greatest integer.\nPlease verify the correctness of my proof:\Consider 1 trillion as a witness. This is a very large number, but 2 trillion is an even bigger number, so 1 trillion is not the greatest integer. Therefore, there isn't a greatest integer, as desired.\n"}, 
            {"role": "assistant", "content": "Your attempt unfortunately doesn't prove the statement: there does not exist a greatest integer. To correctly prove it, you want to show that the statement is true for any arbitrary integer, not just a single value, like 1 trillion. Try to generalize your proof so that it can correctly show that any integer is not the greatest integer."}],
            [{"role": "user", "content": f"I am working on proving the statement:\nproblem_placeholder\nPlease verify the correctness of my proof:\nattempt_placeholder\n"}, 
            {"role": "assistant", "content": "response_placeholder"}]
        ],
        # Witness
        [
            [{"role": "user", "content": f"I am working on proving the statement:\There does not exist a greatest integer.\nPlease verify the correctness of my proof:\Consider 1 trillion as a witness. This is a very large number, but 2 trillion is an even bigger number, so 1 trillion is not the greatest integer. Therefore, there isn't a greatest integer, as desired.\n"}, 
            {"role": "assistant", "content": "Your attempt unfortunately doesn't prove the statement: there does not exist a greatest integer. To correctly prove it, you want to show that the statement is true for any arbitrary integer, not just a single value, like 1 trillion. Try to generalize your proof so that it can correctly show that any integer is not the greatest integer."}],
            [{"role": "user", "content": f"I am working on proving the statement:\nproblem_placeholder\nPlease verify the correctness of my proof:\nattempt_placeholder\n"}, 
            {"role": "assistant", "content": "response_placeholder"}]
        ]
    ]
]

def get_fewshot(stage, proof_strategy, num_examples):
    few_shot_examples = []
    match stage, proof_strategy:
        # Stage 1
        case "Stage 1", "Contradiction":
            few_shot_examples = random.sample(proof_bank[0][0], num_examples)
        case "Stage 1", "Contrapositive":
            few_shot_examples = random.sample(proof_bank[0][1], num_examples)
        case "Stage 1", "Direct":
            few_shot_examples = random.sample(proof_bank[0][2], num_examples)
        case "Stage 1", "Induction":
            few_shot_examples = random.sample(proof_bank[0][3], num_examples)
        case "Stage 1", "Witness":
            few_shot_examples = random.sample(proof_bank[0][4], num_examples)
        case "Stage 1", _:
            few_shot_examples = random.sample(proof_bank[0][random.randint(0, 4)], num_examples)
        # Stage 2
        case "Stage 2", "Contradiction":
            few_shot_examples = random.sample(proof_bank[1][0], num_examples)
        case "Stage 2", "Contrapositive":
            few_shot_examples = random.sample(proof_bank[1][1], num_examples)
        case "Stage 2", "Direct":
            few_shot_examples = random.sample(proof_bank[1][2], num_examples)
        case "Stage 2", "Induction":
            few_shot_examples = random.sample(proof_bank[1][3], num_examples)
        case "Stage 2", "Witness":
            few_shot_examples = random.sample(proof_bank[1][4], num_examples)
        case "Stage 2", _:
            few_shot_examples = random.sample(proof_bank[1][random.randint(0, 4)], num_examples)
        # Stage 3
        case "Stage 3", "Contradiction":
            few_shot_examples = random.sample(proof_bank[2][0], num_examples)
        case "Stage 3", "Contrapositive":
            few_shot_examples = random.sample(proof_bank[2][1], num_examples)
        case "Stage 3", "Direct":
            few_shot_examples = random.sample(proof_bank[2][2], num_examples)
        case "Stage 3", "Induction":
            few_shot_examples = random.sample(proof_bank[2][3], num_examples)
        case "Stage 3", "Witness":
            few_shot_examples = random.sample(proof_bank[2][4], num_examples)
        case "Stage 3", _:
            few_shot_examples = random.sample(proof_bank[2][random.randint(0, 4)], num_examples)
        # Stage 4
        case "Stage 4", "Contradiction":
            few_shot_examples = random.sample(proof_bank[3][0], num_examples)
        case "Stage 4", "Contrapositive":
            few_shot_examples = random.sample(proof_bank[3][1], num_examples)
        case "Stage 4", "Direct":
            few_shot_examples = random.sample(proof_bank[3][2], num_examples)
        case "Stage 4", "Induction":
            few_shot_examples = random.sample(proof_bank[3][3], num_examples)
        case "Stage 4", "Witness":
            few_shot_examples = random.sample(proof_bank[3][4], num_examples)
        case "Stage 4", _:
            few_shot_examples = random.sample(proof_bank[3][random.randint(0, 4)], num_examples)
        case _, _:
            return []
    return few_shot_examples
        
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
        # num_examples = 2
        # fewshot = get_fewshot(stage[0:7], proof_strategy, num_examples)
        # for example in fewshot:
        #     conversation.append(example[0])
        #     conversation.append(example[1])
        conversation.append({"role": "user", "content": f"Proof Statement:\n{proof_statement}\nMy Attempt:\n{user_message}\n"})
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
            proof_strategy = gr.Dropdown(["Contradiction", "Contrapositive", "Direct", "Induction", "Witness"], label="Proof Strategy - Optional", info="Do you know which proof strategy to use?")        
        with gr.Row():
            with gr.Column(scale = 1):
                message = gr.Textbox(label = "Message", lines = 13)
                submit = gr.Button("Send")
            with gr.Column(scale = 2):
                chatbot = gr.Chatbot(show_copy_button = True, height = 345)
                clear = gr.ClearButton([message, chatbot])
        submit.click(get_tutor_response, [message, chatbot, proof_statement, stage, proof_strategy], [message, chatbot])

    tutor.launch(share=True)
    