import os
from openai import OpenAI
import gradio as gr

def get_client() -> OpenAI:
    api_env_key = "OPENAI_API_KEY"
    if not api_env_key in os.environ:
        raise KeyError(f"You must set the environment variable '{api_env_key}'")
    api_key = os.environ[api_env_key]

    org_env_key = "OPENAI_ORG_KEY"
    if not org_env_key in os.environ:
        raise KeyError(f"You must set the environment variable '{org_env_key}'")
    org_key = os.environ[org_env_key]
    return OpenAI(api_key=api_key.strip(), organization=org_key.strip())
  
def get_system_message(stage):
    match stage:
        case "Stage 1":
            return "You are a tutor for an introductory math proof writing class. You are helping a student who does not understand the problem they are working on. Do not give any part of the proof."
        case "Stage 2":
            return "You are a tutor for an introductory math proof writing class. You are helping a student who understands the problem they are working on, but does not know how to begin writing the proof. Suggest which methods of proof may be successful for the problem. Do not give away any part of the proof."
        case "Stage 3":
            return "You are a tutor for an introductory math proof writing class. You are helping a student who has begun writing a proof for the problem statement but doesn’t know how to proceed to a finished proof. Verify whether or not the student is on the right track. If they are on the right track, give a hint for the next step. If they are not on the right track, identify what they did wrong. Do not give away any parts of the correct proof."
        case "Stage 4":
            return "You are a tutor for an introductory math proof writing class. You are helping a student who completed a proof for the problem statement and wants to verify the correctness of their proof. Do not give any part of the proof."

    # -if switch cases don't work-
    # if stage == "Stage 1":
    #         return "You are a tutor for an introductory math proof writing class. You are helping a student who does not understand the problem they are working on. Do not give any part of the proof."
    # elif stage == "Stage 2":
    #         return "You are a tutor for an introductory math proof writing class. You are helping a student who understands the problem they are working on, but does not know how to begin writing the proof. Suggest which methods of proof may be successful for the problem. Do not give away any part of the proof."
    # elif stage ==  "Stage 3":
    #         return "You are a tutor for an introductory math proof writing class. You are helping a student who has begun writing a proof for the problem statement but doesn’t know how to proceed to a finished proof. Verify whether or not the student is on the right track. If they are on the right track, give a hint for the next step. If they are not on the right track, identify what they did wrong. Do not give away any parts of the correct proof."
    # elif stage ==  "Stage 4":
    #         return "You are a tutor for an introductory math proof writing class. You are helping a student who completed a proof for the problem statement and wants to verify the correctness of their proof. Do not give any part of the proof."

def get_gpt_response(
    proof,
    stage,
    user_message,
) -> str:
    conversation = [
        {"role": "system", "content": get_system_message(stage[0:7])},
        {"role": "user", "content": user_message},
    ]
    completion = get_client().chat.completions.create(
        model="gpt-4", messages=conversation, temperature=0
    )
    response = completion.choices[0].message.content
    if response:
        return response
    return "Couldn't get response."

# def greet(proof, stage, user_message):
#     return "Student is working on "  proof + " and is on " + stage[0:7] + "!" + " User message: " + user_message

if __name__ == "__main__":
    demo = gr.Interface(
        fn=get_gpt_response,
        inputs=[gr.Dropdown(
                ["contradiction", "witness", "induction"], label="Proof", info="Which proof would you like assistance on?"
            ),
                gr.Dropdown(
                ["Stage 1: I don't understand the problem", "Stage 2: I don't know how to begin", "Stage 3: I don't know how to proceed", "Stage 4: I completed the proof"], label="Stage", info="What stage of the proof writing process are you on?"
            ),
                "text"],
        outputs=["text"],
    )
    demo.launch(share=True)