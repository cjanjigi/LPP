module

public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace ProbabilityBasics.Liggett

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The block process of (1.9) for block length `k`:
`{X_{nk,(n+1)k}, n ≥ 1}`, with process index `j` standing for `n = j + 1`. -/
def liggettBlockProcess (X : ℕ → ℕ → Ω → ℝ) (k : ℕ) : ℕ → Ω → ℝ :=
  fun j ω => X ((j + 1) * k) ((j + 2) * k) ω

end ProbabilityBasics.Liggett
