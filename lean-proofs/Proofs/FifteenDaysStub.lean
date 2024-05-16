import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic.GCongr
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Nat.Digits

open Nat

namespace Finset

def days := range 104
def days_of_week := range 7

variable {assign: Nat -> Nat}

theorem fifteen_days
  (h: ∀ g ∈ days, assign g ∈ days_of_week):
  ∃ p ∈ days_of_week,
    14 < (days.filter fun g => assign g = p).card := by
