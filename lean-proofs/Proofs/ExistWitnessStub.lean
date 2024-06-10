import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic.GCongr
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Nat.Digits

open Nat

-- Proof by witness
theorem exists_witness: ∃ (n: ℕ), 1 ≤ n ∧ List.length (digits 10 (2 ^ n)) ≠ ⌈(n : ℚ) / 3⌉₊ := by
sorry
