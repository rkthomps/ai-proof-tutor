import os

from openai import OpenAI

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
    api_env_key = "OPENAI_API_KEY"
    if not api_env_key in os.environ:
        raise KeyError(f"You must set the environment variable '{api_env_key}'")
    api_key = os.environ[api_env_key]

    org_env_key = "OPENAI_ORG_KEY"
    if not org_env_key in os.environ:
        raise KeyError(f"You must set the environment variable '{org_env_key}'")
    org_key = os.environ[org_env_key]
    return OpenAI(api_key=api_key.strip(), organization=org_key.strip())
