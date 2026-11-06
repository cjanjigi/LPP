module

public import Mathlib.Data.Fintype.Basic

@[expose] public section

namespace ProbabilityBasics.BK

variable {n : ℕ}

/-- The configuration `ω'` determined by `K(ω') = K`. -/
def configOfOnes (K : Finset (Fin n)) : Fin n → Bool :=
  fun i => decide (i ∈ K)

end ProbabilityBasics.BK
