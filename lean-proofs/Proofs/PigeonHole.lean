

import Mathlib.Data.Finset.Basic
import Mathlib.Combinatorics.Pigeonhole

-- exists_lt_card_fiber_of_mul_lt_card_of_maps_to
-- is from https://github.com/leanprover-community/mathlib4/blob/d73713b9b350dacdbe514d8f1b39c914606b7e8c/Mathlib/Combinatorics/Pigeonhole.lean#L243

namespace Finset

def goodberries := range 50
def party_people := range 6

variable {assign: Nat -> Nat}

theorem nine_goodberries
  (h: ∀ g ∈ goodberries, assign g ∈ party_people):
  ∃ p ∈ party_people,
    8 < (goodberries.filter fun g => assign g = p).card := by
  apply exists_lt_card_fiber_of_mul_lt_card_of_maps_to
  . exact h
  . simp [goodberries, party_people]
