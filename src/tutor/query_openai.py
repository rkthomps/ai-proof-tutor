import os

from openai import OpenAI
from yaml import load, Loader

SECRETS_PATH = "secrets.yaml"


def get_gpt4_response(
    system_message: str,
    user_message: str,
    temperature: float,
    model_name: str,
    client: OpenAI,
) -> str:
    conversation = [
        {"role": "system", "content": system_message},
        {"role": "user", "content": user_message},
    ]

    completion = client.chat.completions.create(
        model=model_name, messages=conversation, temperature=temperature
    )
    response = completion.choices[0].message.content
    if response:
        return response
    return "Couldn't get response."


def get_client() -> OpenAI:
    if not os.path.exists(SECRETS_PATH):
        raise FileNotFoundError(
            (
                f"Could not find {SECRETS_PATH}. Make sure you are in the "
                f"root project directory, and that you have a {SECRETS_PATH} file "
                "with your org key and api key."
            )
        )

    with open(SECRETS_PATH, "r") as fin:
        conf = load(fin, Loader=Loader)

    if not "api_key" in conf:
        raise KeyError(
            (
                f"Your {SECRETS_PATH} file must have your open ai "
                'api key under "api_key".'
            )
        )
    api_key: str = conf["api_key"]

    if not "org_key" in conf:
        raise KeyError(
            (
                f"Your {SECRETS_PATH} file must have your open ai "
                'org key under "org_key".'
            )
        )
    org_key: str = conf["org_key"]
    return OpenAI(api_key=api_key.strip(), organization=org_key.strip())
