module

public import ProbabilityBasics.Frozen.Foundations.BK.IsWitnessSet
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.Disjoint

@[expose] public section

namespace ProbabilityBasics.BK

variable {ι : Type*} {E : ι → Type*}

/-- Disjoint occurrence `A □ B`: two disjoint finite sets of coordinates
witness `A` and `B` respectively. -/
def boxOccurrence (A B : Set (∀ i, E i)) : Set (∀ i, E i) :=
  {ω | ∃ K L : Finset ι, Disjoint K L ∧
    IsWitnessSet A (K : Set ι) ω ∧ IsWitnessSet B (L : Set ι) ω}

end ProbabilityBasics.BK
