module

public import ProbabilityBasics.Frozen.Foundations.BK.IsWitnessSet
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.Disjoint

@[expose] public section

namespace ProbabilityBasics.BK

variable {ι : Type*} {E : ι → Type*}

/-- Disjoint occurrence of a family `A j`: pairwise disjoint finite sets of
coordinates witness the events `A j` respectively. -/
def disjointOccurrence {J : Type*} (A : J → Set (∀ i, E i)) : Set (∀ i, E i) :=
  {ω | ∃ K : J → Finset ι, Pairwise (fun j l => Disjoint (K j) (K l)) ∧
    ∀ j, IsWitnessSet (A j) (K j : Set ι) ω}

end ProbabilityBasics.BK
