import sys, os
import argparse
from openai import OpenAI

from tutor.query_openai import get_gpt4_response, get_client


def read_file(file_path: str) -> str:
    with open(file_path, "r") as fin:
        return fin.read()


def get_tutor_response(
    theorem_statement: str, proof_attempt: str, ground_truth_proof: str, client: OpenAI
) -> str:
    system_message = "Hi"
    user_message = "Hi"
    temperature = 0
    model_name = "gpt-4"
    return get_gpt4_response(
        system_message,
        user_message,
        temperature,
        model_name,
        client,
    )


def format_response(
    theorem_statement: str, proof_attempt: str, ground_truth_proof: str, response: str
) -> str:
    return (
        f"Theorem Statement:\n{theorem_statement}\n\n"
        f"Correct Proof:\n{ground_truth_proof}\n\n"
        f"Proof Attempt:\n{proof_attempt}\n\n"
        f"Response:\n{response}"
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        "Command line interface (CLI) for CSE 21 AI Tutor."
    )
    parser.add_argument(
        "theorem_statement_path", help="Path to file with theorem statement."
    )
    parser.add_argument(
        "proof_attempt_path", help="Path to file with student proof attempt."
    )
    parser.add_argument(
        "ground_truth_proof_path", help="Path to file with ground truth proof."
    )
    args = parser.parse_args(sys.argv[1:])

    theorem_statement = read_file(args.theorem_statement_path)
    proof_attempt = read_file(args.proof_attempt_path)
    ground_truth_proof = read_file(args.ground_truth_proof_path)
    client = get_client()

    response = get_tutor_response(
        theorem_statement, proof_attempt, ground_truth_proof, client
    )
    print(
        format_response(theorem_statement, proof_attempt, ground_truth_proof, response)
    )
