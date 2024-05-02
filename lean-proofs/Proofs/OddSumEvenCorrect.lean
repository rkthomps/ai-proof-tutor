import Mathlib.Tactic.Linarith

def even(x: Nat): Prop := ∃ (k: Nat), x = 2 * k
def odd(x: Nat): Prop := ∃ (k: Nat), x = 2 * k + 1

theorem odd_sum_even: ∀ x y, odd x -> odd y -> even (x + y) := by
  intros x y h1 h2 -- Introduce x and y as arbitrary integers and assume h1: odd x and h2: odd y
  unfold odd at h1 -- Expand the definition of odd for x, i.e., x = 2a + 1 for some integer a
  unfold odd at h2 -- Expand the definition of odd for y, i.e., y = 2b + 1 for some integer b
  cases h1 with -- Extract the specific integer a (k1 in the proof) such that x = 2k1 + 1
  | intro k1 hk1 =>
    cases h2 with -- Extract the specific integer b (k2 in the proof) such that y = 2k2 + 1
    | intro k2 hk2 =>
      exists (k1 + k2 + 1) -- Define an integer (k1 + k2 + 1) to show x+y is even
      rw [hk1] -- Rewrite x in the equation using x = 2k1 + 1
      rw [hk2] -- Rewrite y in the equation using y = 2k2 + 1
      rw [<- Nat.add_assoc] -- Use associativity of addition to rearrange terms
      linarith -- Linear arithmetic to conclude x+y = 2(k1 + k2 + 1), showing that the sum of any two odd integers is even. 


