import sys, os
import argparse
from openai import OpenAI
import gradio as gr
import time
import random

from tutor.query_openai import get_gpt4_response, get_client
from tutor.check_formal_proof import get_formal_checker_response


# def read_file(file_path: str) -> str:
#     with open(file_path, "r") as fin:
#         return fin.read()

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

def get_conversation(stage, proof_strategy):
    conversation = []
    few_shot_examples = []
    match stage, proof_strategy:
        # Stage 1
        case "Stage 1", "Contradiction":
            conversation = [{"role": "system", "content": "You are a tutor for an introductory math proof writing class. You are helping a student who does not understand the problem they are working on. Do not give any part of the proof.\n"}]
            few_shot_examples = random.sample(proof_bank[0][0], 2)
        case "Stage 1", "Contrapositive":
            conversation = [{"role": "system", "content": "You are a tutor for an introductory math proof writing class. You are helping a student who does not understand the problem they are working on. Do not give any part of the proof.\n"}]
            few_shot_examples = random.sample(proof_bank[0][1], 2)
        case "Stage 1", "Direct":
            conversation = [{"role": "system", "content": "You are a tutor for an introductory math proof writing class. You are helping a student who does not understand the problem they are working on. Do not give any part of the proof.\n"}]
            few_shot_examples = random.sample(proof_bank[0][2], 2)
        case "Stage 1", "Induction":
            conversation = [{"role": "system", "content": "You are a tutor for an introductory math proof writing class. You are helping a student who does not understand the problem they are working on. Do not give any part of the proof.\n"}]
            few_shot_examples = random.sample(proof_bank[0][3], 2)
        case "Stage 1", "Witness":
            conversation = [{"role": "system", "content": "You are a tutor for an introductory math proof writing class. You are helping a student who does not understand the problem they are working on. Do not give any part of the proof.\n"}]
            few_shot_examples = random.sample(proof_bank[0][4], 2)
        case "Stage 1", _:
            conversation = [{"role": "system", "content": "You are a tutor for an introductory math proof writing class. You are helping a student who does not understand the problem they are working on. Do not give any part of the proof.\n"}]
            few_shot_examples = random.sample(proof_bank[0][random.randint(0, 4)], 2)
        # Stage 2
        case "Stage 2", "Contradiction":
            conversation = [{"role": "system", "content": "You are a tutor for an introductory math proof writing class. You are helping a student who understands the problem they are working on, but does not know how to begin writing the proof. Suggest which methods of proof may be successful for the problem. Do not give away any part of the proof.\n"}]
            few_shot_examples = random.sample(proof_bank[1][0], 2)
        case "Stage 2", "Contrapositive":
            conversation = [{"role": "system", "content": "You are a tutor for an introductory math proof writing class. You are helping a student who understands the problem they are working on, but does not know how to begin writing the proof. Suggest which methods of proof may be successful for the problem. Do not give away any part of the proof.\n"}]
            few_shot_examples = random.sample(proof_bank[1][1], 2)
        case "Stage 2", "Direct":
            conversation = [{"role": "system", "content": "You are a tutor for an introductory math proof writing class. You are helping a student who understands the problem they are working on, but does not know how to begin writing the proof. Suggest which methods of proof may be successful for the problem. Do not give away any part of the proof.\n"}]
            few_shot_examples = random.sample(proof_bank[1][2], 2)
        case "Stage 2", "Induction":
            conversation = [{"role": "system", "content": "You are a tutor for an introductory math proof writing class. You are helping a student who understands the problem they are working on, but does not know how to begin writing the proof. Suggest which methods of proof may be successful for the problem. Do not give away any part of the proof.\n"}]
            few_shot_examples = random.sample(proof_bank[1][3], 2)
        case "Stage 2", "Witness":
            conversation = [{"role": "system", "content": "You are a tutor for an introductory math proof writing class. You are helping a student who understands the problem they are working on, but does not know how to begin writing the proof. Suggest which methods of proof may be successful for the problem. Do not give away any part of the proof.\n"}]
            few_shot_examples = random.sample(proof_bank[1][4], 2)
        case "Stage 2", _:
            conversation = [{"role": "system", "content": "You are a tutor for an introductory math proof writing class. You are helping a student who understands the problem they are working on, but does not know how to begin writing the proof. Suggest which methods of proof may be successful for the problem. Do not give away any part of the proof.\n"}]
            few_shot_examples = random.sample(proof_bank[1][random.randint(0, 4)], 2)
        # Stage 3
        case "Stage 3", "Contradiction":
            conversation = [{"role": "system", "content": "You are a tutor for an introductory math proof writing class. You are helping a student who has begun writing a proof for the problem statement but doesn’t know how to proceed to a finished proof. Verify whether or not the student is on the right track. If they are on the right track, give a hint for the next step. If they are not on the right track, identify what they did wrong. Do not give away any parts of the correct proof.\n"}]
            few_shot_examples = random.sample(proof_bank[2][0], 2)
        case "Stage 3", "Contrapositive":
            conversation = [{"role": "system", "content": "You are a tutor for an introductory math proof writing class. You are helping a student who has begun writing a proof for the problem statement but doesn’t know how to proceed to a finished proof. Verify whether or not the student is on the right track. If they are on the right track, give a hint for the next step. If they are not on the right track, identify what they did wrong. Do not give away any parts of the correct proof.\n"}]
            few_shot_examples = random.sample(proof_bank[2][1], 2)
        case "Stage 3", "Direct":
            conversation = [{"role": "system", "content": "You are a tutor for an introductory math proof writing class. You are helping a student who has begun writing a proof for the problem statement but doesn’t know how to proceed to a finished proof. Verify whether or not the student is on the right track. If they are on the right track, give a hint for the next step. If they are not on the right track, identify what they did wrong. Do not give away any parts of the correct proof.\n"}]
            few_shot_examples = random.sample(proof_bank[2][2], 2)
        case "Stage 3", "Induction":
            conversation = [{"role": "system", "content": "You are a tutor for an introductory math proof writing class. You are helping a student who has begun writing a proof for the problem statement but doesn’t know how to proceed to a finished proof. Verify whether or not the student is on the right track. If they are on the right track, give a hint for the next step. If they are not on the right track, identify what they did wrong. Do not give away any parts of the correct proof.\n"}]
            few_shot_examples = random.sample(proof_bank[2][3], 2)
        case "Stage 3", "Witness":
            conversation = [{"role": "system", "content": "You are a tutor for an introductory math proof writing class. You are helping a student who has begun writing a proof for the problem statement but doesn’t know how to proceed to a finished proof. Verify whether or not the student is on the right track. If they are on the right track, give a hint for the next step. If they are not on the right track, identify what they did wrong. Do not give away any parts of the correct proof.\n"}]
            few_shot_examples = random.sample(proof_bank[2][4], 2)
        case "Stage 3", _:
            conversation = [{"role": "system", "content": "You are a tutor for an introductory math proof writing class. You are helping a student who has begun writing a proof for the problem statement but doesn’t know how to proceed to a finished proof. Verify whether or not the student is on the right track. If they are on the right track, give a hint for the next step. If they are not on the right track, identify what they did wrong. Do not give away any parts of the correct proof.\n"}]
            few_shot_examples = random.sample(proof_bank[2][random.randint(0, 4)], 2)
        # Stage 4
        case "Stage 4", "Contradiction":
            conversation = [{"role": "system", "content": "You are a tutor for an introductory math proof writing class. You are helping a student who completed a proof for the problem statement and wants to verify the correctness of their proof. Do not give any part of the proof.\n"}]
            few_shot_examples = random.sample(proof_bank[3][0], 2)
        case "Stage 4", "Contrapositive":
            conversation = [{"role": "system", "content": "You are a tutor for an introductory math proof writing class. You are helping a student who completed a proof for the problem statement and wants to verify the correctness of their proof. Do not give any part of the proof.\n"}]
            few_shot_examples = random.sample(proof_bank[3][1], 2)
        case "Stage 4", "Direct":
            conversation = [{"role": "system", "content": "You are a tutor for an introductory math proof writing class. You are helping a student who completed a proof for the problem statement and wants to verify the correctness of their proof. Do not give any part of the proof.\n"}]
            few_shot_examples = random.sample(proof_bank[3][2], 2)
        case "Stage 4", "Induction":
            conversation = [{"role": "system", "content": "You are a tutor for an introductory math proof writing class. You are helping a student who completed a proof for the problem statement and wants to verify the correctness of their proof. Do not give any part of the proof.\n"}]
            few_shot_examples = random.sample(proof_bank[3][3], 2)
        case "Stage 4", "Witness":
            conversation = [{"role": "system", "content": "You are a tutor for an introductory math proof writing class. You are helping a student who completed a proof for the problem statement and wants to verify the correctness of their proof. Do not give any part of the proof.\n"}]
            few_shot_examples = random.sample(proof_bank[3][4], 2)
        case "Stage 4", _:
            conversation = [{"role": "system", "content": "You are a tutor for an introductory math proof writing class. You are helping a student who completed a proof for the problem statement and wants to verify the correctness of their proof. Do not give any part of the proof.\n"}]
            few_shot_examples = random.sample(proof_bank[3][random.randint(0, 4)], 2)
        case _, _:
            return []
    return conversation + few_shot_examples[0] + few_shot_examples[1]
        
    # -if switch cases don't work-
    # if stage == "Stage 1":
    #         conversation = [{"role": "system", "content": "You are a tutor for an introductory math proof writing class. You are helping a student who does not understand the problem they are working on. Do not give any part of the proof.\n"}]
    #         # return conversation + proof_bank[0][0] + proof_bank[0][1]
    #         choice = random.sample(proof_bank[0], 1)
    #         return conversation + choice[0] # + choice[1]
    # elif stage == "Stage 2":
    #         conversation = [{"role": "system", "content": "You are a tutor for an introductory math proof writing class. You are helping a student who understands the problem they are working on, but does not know how to begin writing the proof. Suggest which methods of proof may be successful for the problem. Do not give away any part of the proof.\n"}]
    #         return conversation + proof_bank[1][0] + proof_bank[1][1]
    # elif stage == "Stage 3":
    #         conversation = [{"role": "system", "content": "You are a tutor for an introductory math proof writing class. You are helping a student who has begun writing a proof for the problem statement but doesn’t know how to proceed to a finished proof. Verify whether or not the student is on the right track. If they are on the right track, give a hint for the next step. If they are not on the right track, identify what they did wrong. Do not give away any parts of the correct proof.\n"}]
    #         return conversation + proof_bank[2][0] + proof_bank[2][1]
    # elif stage == "Stage 4":
    #         conversation = [{"role": "system", "content": "You are a tutor for an introductory math proof writing class. You are helping a student who completed a proof for the problem statement and wants to verify the correctness of their proof. Do not give any part of the proof.\n"}]
    #         return conversation + proof_bank[3][0] + proof_bank[3][1]

def get_tutor_response(user_message, chat_history, proof_statement, stage, proof_strategy):
    conversation = []
    # initial query (few shot)
    if chat_history == []:
        conversation = get_conversation(stage[0:7], proof_strategy)
        conversation.append({"role": "user", "content": f"I am working on the proof:\n{proof_statement}\n{user_message}\n"})
        # print(conversation)
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
    if stage[0:7] == "Stage 4" and not get_formal_checker_response(user_message, proof_statement):
        print("formal proof incorrect")
        conversation.pop()
        # feed back to GPT-4, but mention attempt is incorrect
        conversation.append(({"role": "user", "content": f"I am working on the proof:\n{proof_statement}\nMy proof attempt is incorrect, please guide me.\n{user_message}\n"}))
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
    