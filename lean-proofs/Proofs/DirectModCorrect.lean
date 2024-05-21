import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic.GCongr
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Nat.Digits

open Nat

-- Direct proof
theorem direct_mod: ∀ (a b m : ℤ), 2 ≤ m → a % m = b % m → a^3 % m = b^3 % m := by
  intro a b m H1 H2
  -- repeat rw [pow_three]
  -- nth_rewrite 1 [Int.mul_emod]
  -- nth_rewrite 2 [Int.mul_emod]
  -- nth_rewrite 3 [Int.mul_emod]
  -- nth_rewrite 4 [Int.mul_emod]
  -- rw [H2]
  simp [pow_three, Int.mul_emod, H2]
