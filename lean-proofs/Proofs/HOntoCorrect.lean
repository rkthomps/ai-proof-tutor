import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic.GCongr
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Nat.Digits

open Nat

-- Proof by cases
def h_dom : Set ℚ := {x | -1 < x ∧ x ≤  1}
def h_rng : Set ℚ := {x | 0 ≤ x}

def h (x : ℚ) := if  0 < x then 1 / x else -x

attribute [local simp] h_dom h_rng h

#eval h 0

theorem h_onto: ∀ y ∈ h_rng, ∃ x ∈ h_dom, h x = y := by
  intro y H
  by_cases Hy : 1 ≤ y
  . exists 1 / y; simp at *
    constructor
    . constructor
      . apply @lt_trans _ _ _ 0 <;> simp
        apply @lt_of_lt_of_le _ _ 0 1 y <;> simp [Hy]
      . apply inv_le_one; exact Hy
      --. have h1: 0 < y := by linarith
      --  rw [← inv_pos] at h1; linarith
      --. apply inv_le_one; exact hy
    . intro H1; absurd H1; linarith
  . exists -y; simp at *
    constructor
    . constructor
      . linarith
      . linarith
    . intro h1; linarith
