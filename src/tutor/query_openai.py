import os

from openai import OpenAI

SECRETS_PATH = "secrets.yaml"


def get_gpt4_response(
    conversation,
    temperature: float,
    model_name: str,
) -> str:
    # conversation = [{"role": "system", "content": system_message}]
    
    # for index in range(len(user_message)):
    #     if (index < len(user_message)):
    #         conversation.append({"role": "user", "content": user_message[index]})
    #     if (index < len(assistant_message)):
    #         conversation.append({"role": "assistant", "content": assistant_message[index]})

    # conversation = [
    #     {"role": "system", "content": system_message},
    #     {"role": "user", "content": user_message[0]},
    # ]

    # if (assistant_message != "")
    #     conversation.insert(1, {"role": "assistant", "content": assistant_message[0]})

    completion = get_client().chat.completions.create(
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
