module

public import ProbabilityBasics.Frozen.Foundations.BK.AgreementCylinder
public import Mathlib.Data.Set.Defs

@[expose] public section

namespace ProbabilityBasics.BK

variable {ι : Type*} {E : ι → Type*}

/-- The coordinates in `K` witness the event `A` at `ω`: every configuration
that agrees with `ω` on `K` lies in `A`. -/
def IsWitnessSet (A : Set (∀ i, E i)) (K : Set ι) (ω : ∀ i, E i) : Prop :=
  agreementCylinder K ω ⊆ A

end ProbabilityBasics.BK
