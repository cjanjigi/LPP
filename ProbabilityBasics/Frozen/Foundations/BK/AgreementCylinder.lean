module

public import Mathlib.Data.Set.Defs

@[expose] public section

namespace ProbabilityBasics.BK

variable {ι : Type*} {E : ι → Type*}

/-- van den Berg–Kesten's cylinder `C(K, ω)`: the configurations that agree
with `ω` at every coordinate in `K`. -/
def agreementCylinder (K : Set ι) (ω : ∀ i, E i) : Set (∀ i, E i) :=
  {ω' | ∀ i ∈ K, ω' i = ω i}

end ProbabilityBasics.BK
