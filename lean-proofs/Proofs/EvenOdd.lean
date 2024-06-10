import Mathlib.Tactic.Linarith

def even(x: Nat): Prop := ∃ (k: Nat), x = 2 * k
def odd(x: Nat): Prop := ∃ (k: Nat), x = 2 * k + 1

theorem two_even: even 2 := by
  unfold even
  exists 1

-- theorem odd_not_even: ∀ x, odd x -> ¬ even x := by
--   intros x
--   intros h
--   unfold odd at h
--   cases h with
--   | intro k1 hk1 =>
--     unfold even
--     rw [hk1]
--     sorry

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



theorem all_nat_even_or_odd: ∀ x, odd x ∨ even x := by
  intro x; induction x with
  | zero        =>
    apply Or.intro_right
    unfold even
    exists 0
  | succ n ihn  =>
    cases ihn
    case inr h =>
      apply Or.inl
      unfold even at h
      cases h with
      | intro hk hn =>
        unfold odd
        exists hk
        rw [hn]
    case inl h =>
      apply Or.inr
      unfold odd at h
      cases h with
      | intro ho hn =>
        unfold even
        exists ho + 1
        linarith
