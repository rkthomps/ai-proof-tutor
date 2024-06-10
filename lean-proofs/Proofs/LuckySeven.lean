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


-- Proof by witness
theorem exists_witness: ∃ (n: ℕ), 1 ≤ n ∧ List.length (digits 10 (2 ^ n)) ≠ ⌈(n : ℚ) / 3⌉₊ := by
  apply Exists.intro 13
  have hc : ⌈(13 : ℚ) / 3⌉₊ = 5 := by rfl
  simp [hc]



-- Proof by contradiction
-- -- So making the argument "Assume the maximum number of the 104 day that fall on the same day of the week is ..."
   -- is hard in lean
   -- So I will prove this by the pigeonhole principle for now.

-- exists_lt_card_fiber_of_mul_lt_card_of_maps_to
-- is from https://github.com/leanprover-community/mathlib4/blob/d73713b9b350dacdbe514d8f1b39c914606b7e8c/Mathlib/Combinatorics/Pigeonhole.lean#L243
namespace Finset

def days := range 104
def days_of_week := range 7

variable {assign: Nat -> Nat}

theorem fifteen_days
  (h: ∀ g ∈ days, assign g ∈ days_of_week):
  ∃ p ∈ days_of_week,
    14 < (days.filter fun g => assign g = p).card := by
  apply exists_lt_card_fiber_of_mul_lt_card_of_maps_to
  . exact h
  . simp [days, days_of_week]


-- Proof by counterexample


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
