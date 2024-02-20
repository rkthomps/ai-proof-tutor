
import Mathlib.Tactic.Linarith

def even(x: Nat): Prop := ∃ (k: Nat), x = 2 * k
def odd(x: Nat): Prop := ∃ (k: Nat), x = 2 * k + 1

theorem odd_sum_even: ∀ x y, odd x -> odd y -> even (x + y) := by
sorry
