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
intro n
induction' n using Nat.strong_induction_on with n ih
unfold r
cases n with
| zero => simp
| succ n' => cases n' with
  | zero => simp
  | succ n'' =>
    simp
    rw [ih]; rw[ih]; ring_nf;
    rw [Nat.pow_succ]; rw [Nat.pow_succ]; rw[Nat.pow_succ]; ring_nf
    rw [<- Nat.sub_sub];
    have h: ∀ (m:ℕ), 4 + m * 24 - 3 = 1 + m * 24 := by
      intro m; rw [Nat.add_comm]; simp; rw [Nat.add_comm]
    rw [h]; rw [Nat.add_sub_assoc]; rw [← Nat.mul_sub_left_distrib]; ring_nf
    apply Nat.mul_le_mul_left; norm_num; linarith; linarith
