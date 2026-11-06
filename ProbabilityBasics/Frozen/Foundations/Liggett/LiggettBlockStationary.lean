module

public import ProbabilityBasics.Frozen.Foundations.Liggett.IsStationaryProcess
public import ProbabilityBasics.Frozen.Foundations.Liggett.LiggettBlockProcess

@[expose] public section

open MeasureTheory

namespace ProbabilityBasics.Liggett

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Liggett (1.9): for each `k ≥ 1` the block process is stationary. -/
def LiggettBlockStationary (μ : Measure Ω) (X : ℕ → ℕ → Ω → ℝ) : Prop :=
  ∀ k : ℕ, 0 < k → IsStationaryProcess μ (liggettBlockProcess X k)

end ProbabilityBasics.Liggett
