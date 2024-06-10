import os
from openai import OpenAI

# Path to the secrets file (currently unused)
SECRETS_PATH = "secrets.yaml"

def get_gpt4_response(conversation: list, temperature: float, model_name: str) -> str:
    """
    Get a response from GPT-4 based on the provided conversation.

    Parameters:
    conversation (list): List of message dictionaries for the conversation.
    temperature (float): Sampling temperature for the response.
    model_name (str): Name of the GPT-4 model to use.

    Returns:
    str: The response from GPT-4, or an error message if the response is empty.
    """
    # Create a completion using the OpenAI client
    completion = get_client().chat.completions.create(
        model=model_name, messages=conversation, temperature=temperature
    )
    
    # Extract the response content
    response = completion.choices[0].message.content
    
    # Return the response if available, otherwise return an error message
    if response:
        return response
    return "Couldn't get response."

def get_client() -> OpenAI:
    """
    Initialize and return an OpenAI client using API and organization keys from environment variables.

    Returns:
    OpenAI: An instance of the OpenAI client.

    Raises:
    KeyError: If the required environment variables are not set.
    """
    # Define the environment variable keys
    api_env_key = "OPENAI_API_KEY"
    org_env_key = "OPENAI_ORG_KEY"
    
    # Check and retrieve the API key from environment variables
    if api_env_key not in os.environ:
        raise KeyError(f"You must set the environment variable '{api_env_key}'")
    api_key = os.environ[api_env_key]
    
    # Check and retrieve the organization key from environment variables
    if org_env_key not in os.environ:
        raise KeyError(f"You must set the environment variable '{org_env_key}'")
    org_key = os.environ[org_env_key]
    
    # Initialize and return the OpenAI client
    return OpenAI(api_key=api_key.strip(), organization=org_key.strip())
