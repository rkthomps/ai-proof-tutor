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
intros n;
induction n with n ih;
cases n with n;
simp only [r, pow_zero, mul_one, add_zero];
try {simp only [r, pow_one, mul_two, add_comm]};
try {have h₁ : ∀ m, m < succ (succ n) → r m = 2 * (3 ^ m) + 1 := by intros m hm; exact ih m (lt_trans hm (lt_add_one _))};
try {simp only [r, h₁, pow_succ, mul_add, mul_one, add_left_inj, mul_assoc, mul_left_comm]};
try {ring_exp at ⊢};
try {exact rfl}
