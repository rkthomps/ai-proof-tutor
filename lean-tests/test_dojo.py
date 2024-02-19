import os
from lean_dojo import LeanGitRepo, Theorem, Dojo
import ipdb


repo = LeanGitRepo("https://github.com/yangky11/lean4-example", "fd14c4c8b29cc74a082e5ae6f64c2fb25b28e15e")
theorem = Theorem(repo, "Lean4Example.lean", "hello_world")

with Dojo(theorem) as (dojo, init_state):
  print(init_state)
  ipdb.set_trace()

# lgr = LeanGitRepo("https://github.com/rkthomps/ai-tutor-lean-proofs", "a9a998af85ea11edf2594ddd57ad1113afb5dc0a")
# thm = Theorem(lgr, "test_proofs/evan_odd.lean", "odd_sum_even")

# with Dojo(thm) as (dojo, init_state):
#     print(init_state)
#     ipdb.set_trace()

