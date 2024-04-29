import Mathlib.Data.Finset.Basic
import Mathlib.Combinatorics.Pigeonhole

namespace Finset

def goodberries := range 50
def party_people := range 6

variable {assign: Nat -> Nat}

theorem nine_goodberries
  (h: ∀ g ∈ goodberries, assign g ∈ party_people):
  ∃ p ∈ party_people,
    8 < (goodberries.filter fun g => assign g = p).card := by
  sorry
