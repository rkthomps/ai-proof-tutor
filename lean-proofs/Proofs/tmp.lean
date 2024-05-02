
import Mathlib.Tactic.Linarith

def even(x: Nat): Prop := ∃ (k: Nat), x = 2 * k
def odd(x: Nat): Prop := ∃ (k: Nat), x = 2 * k + 1

theorem odd_sum_even: ∀ x y, odd x -> odd y -> even (x + y) := by
  intros x y h1 h2
  unfold odd at h1
  unfold odd at h2
  cases h1 with
  | intro k1 hk1 =>
    cases h2 with
    | intro k2 hk2 =>
      exists (k1 + k2 + 1)
      rw [hk1]
      rw [hk2]
      rw [<- Nat.add_assoc]
      linarith
