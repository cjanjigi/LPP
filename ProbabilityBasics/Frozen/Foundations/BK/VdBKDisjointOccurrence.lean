module

public import ProbabilityBasics.Frozen.Foundations.BK.OnesOf
public import ProbabilityBasics.Frozen.Foundations.BK.ConfigOfOnes
public import Mathlib.Data.Fintype.Basic

@[expose] public section

namespace ProbabilityBasics.BK

variable {n : ℕ}

/-- The source's `A ∘ B` for increasing events (p. 562): some `K' ⊆ K(ω)` has
the configuration with ones `K'` in `A` and the configuration with ones
`K(ω) \ K'` in `B`. -/
def vdBKDisjointOccurrence (A B : Set (Fin n → Bool)) : Set (Fin n → Bool) :=
  {ω | ∃ K' ⊆ onesOf ω, configOfOnes K' ∈ A ∧ configOfOnes (onesOf ω \ K') ∈ B}

end ProbabilityBasics.BK
