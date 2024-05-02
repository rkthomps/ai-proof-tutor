import Mathlib.Tactic.Linarith

def even(x: Nat): Prop := ∃ (k: Nat), x = 2 * k
def odd(x: Nat): Prop := ∃ (k: Nat), x = 2 * k + 1

theorem odd_sum_even: ∀ x y, odd x -> odd y -> even (x + y) := by
import Mathlib.Tactic.Linarith

def even(x: Nat): Prop := ∃ (k: Nat), x = 2 * k
def odd(x: Nat): Prop := ∃ (k: Nat), x = 2 * k + 1

theorem odd_sum_even: ∀ x y, odd x -> odd y -> even (x + y) := by
  intros x y h1 h2
  cases h1 with a ha
  cases h2 with b hb
  use a + b + 1
  rw [ha, hb]
  linarith
