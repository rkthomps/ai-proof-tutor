
import Mathlib.Tactic.Linarith

def even(x: Nat): Prop := ∃ (k: Nat), x = 2 * k
def odd(x: Nat): Prop := ∃ (k: Nat), x = 2 * k + 1

theorem odd_sum_even: ∀ x y, odd x -> odd y -> even (x + y) := by
intros x y hx hy;
cases hx with k1 hk1;
cases hy with k2 hk2;
use (k1 + k2 + 1);
split;
rw [Nat.mul_add, Nat.mul_one, hk1, hk2];
simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
