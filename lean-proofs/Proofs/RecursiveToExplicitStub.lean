import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic.GCongr
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Nat.Digits

open Nat

-- Proof by strong induction
def r:  ℕ -> ℕ
  | zero => 3
  | succ (succ n'') => (4 * r (succ n'')) - (3 * r n'')
  | succ _ => 7

attribute [local simp] r

#eval r 4
#eval (2 * (3 ^ 4)) + 1

theorem r_eq: ∀ (n : Nat), r n = 2 * (3 ^ n) + 1 := by
sorry
