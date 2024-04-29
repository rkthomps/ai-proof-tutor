
import Mathlib.Data.Nat.Factorial.Basic

open Nat

-- Theorems about power: https://github.com/leanprover/lean4/blob/master/src/Init/Data/Nat/Basic.lean
-- Theorems about factorial: https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Data/Nat/Factorial/Basic.lean

theorem exp_3_lt_fac: ∀ (n: Nat),
  3^(n + 7) < ((n + 7)!) := by
  intro n; induction n with
  | zero => simp [factorial]
  | succ n' ihn' =>
    rw [Nat.pow_succ]
    rw [Nat.factorial]
    rw [Nat.mul_comm (succ n' + 7)]
    apply mul_lt_mul
    . apply ihn'
    . apply Nat.le_add_left
    . simp
    . simp
