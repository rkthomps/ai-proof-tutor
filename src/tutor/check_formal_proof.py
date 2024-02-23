import argparse
import sys, os
import ipdb
from dataclasses import dataclass
import subprocess
import re

from tutor.query_openai import get_gpt4_response, get_client


@dataclass(frozen=True)
class ProofCheckResult:
    correct: bool
    msg: str

lean_lib_template = """
lean_lib «{:s}» {{
    srcDir := \"{:s}\"
}}
"""

LAKEFILE_NAME = "lakefile.lean"
TMP_LAKEFILE_NAME = "tmp-lakefile.lean"
TMP_OUT_LOC = "out"

STUB_PROJECT_PATH = os.path.join(".", "lean-proofs")
PROOF_DIR = "Proofs"

def __get_contents(file: str) -> str:
    with open(file, "r") as fin:
        return fin.read()

def __write_temp_lakefile(stub_no_lean_name: str) -> None: 
    lakefile_loc = os.path.join(STUB_PROJECT_PATH, LAKEFILE_NAME)
    orig_lakefile_contents = __get_contents(lakefile_loc)
    lean_lib_contents = lean_lib_template.format(stub_no_lean_name, PROOF_DIR)
    new_lakefile_contents = f"{orig_lakefile_contents}\n{lean_lib_contents}"
    tmp_lakefile_loc = os.path.join(STUB_PROJECT_PATH, TMP_LAKEFILE_NAME)
    with open(tmp_lakefile_loc, "w") as fout:
        fout.write(new_lakefile_contents)


def check_proof(formal_proof: str, stub_no_lean_name: str) -> ProofCheckResult:
    assert not os.path.exists(TMP_OUT_LOC)
    stub_lean_name = f"{stub_no_lean_name}.lean"
    stub_loc = os.path.join(STUB_PROJECT_PATH, PROOF_DIR, stub_lean_name)
    stub_contents = __get_contents(stub_loc) 
    stub_new_contents = stub_contents.replace("sorry", formal_proof)
    cur_dir = os.path.abspath(os.curdir)
    temp_lakefile_loc = os.path.join(STUB_PROJECT_PATH, TMP_LAKEFILE_NAME)
    try:
        with open(stub_loc, "w") as fout:
            fout.write(stub_new_contents)
        __write_temp_lakefile(stub_no_lean_name)
        os.chdir(STUB_PROJECT_PATH)
        # ipdb.set_trace()
        with open(TMP_OUT_LOC, "w") as fout:
            result = subprocess.run(["lake", "build", "-f", TMP_LAKEFILE_NAME, stub_no_lean_name], stdout=fout, stderr=fout)
        return_code = result.returncode
        msg = __get_contents(TMP_OUT_LOC) 
        return ProofCheckResult(return_code == 0 and "error" not in msg, msg)
    finally:
        os.chdir(cur_dir)
        if os.path.exists(temp_lakefile_loc):
            os.remove(temp_lakefile_loc)
        out_loc = os.path.join(STUB_PROJECT_PATH, TMP_OUT_LOC)
        if os.path.exists(out_loc):
            os.remove(out_loc)
        with open(stub_loc, "w") as fout:
            fout.write(stub_contents)

def get_formal_checker_response(informal_proof: str, proof_statement:str):
    conversation = [{"role": "system", "content": "You are a proof translator. You take as input natural language proofs and you produce formal proofs in the Lean 4 programming language. No explanation included, pure Lean 4 formal proof."}]
    conversation.append({"role": "user", "content": informal_proof})
    temperature = 0
    model_name = "gpt-4"
    formal_proof = get_gpt4_response(
        conversation,
        temperature,
        model_name
    )
    print(formal_proof)
    pattern = r'begin\n(.*?)\nend'
    formal_proof = re.search(pattern, formal_proof, re.DOTALL).group(1)
    print(formal_proof)
    result = check_proof(formal_proof, proof_statement + "Stub")
    print(result)
    return result.correct

if __name__ == "__main__":
    test_proof = """\
intros x y h1 h2
unfold odd at h1
unfold odd at h2
cases h1 with
| intro k1 hk1 =>
cases h2 with
| intro k2 hk2 =>
    exists (k1 + k2 + 1)
    rw [hk1]
    rw [hk2]
    rw [<- Nat.add_assoc]
    linarith
"""

# print(check_proof(test_proof, "OddSumStub"))
    