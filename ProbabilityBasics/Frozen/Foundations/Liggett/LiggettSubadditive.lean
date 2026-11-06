module

public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Basic.Real.Basic

@[expose] public section

open MeasureTheory

namespace ProbabilityBasics.Liggett

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Liggett (1.7): `X_{0,n} ≤ X_{0,m} + X_{m,n}` whenever `0 < m < n`,
as an almost-sure inequality of random variables. -/
def LiggettSubadditive (μ : Measure Ω) (X : ℕ → ℕ → Ω → ℝ) : Prop :=
  ∀ m n : ℕ, 0 < m → m < n → ∀ᵐ ω ∂μ, X 0 n ω ≤ X 0 m ω + X m n ω

end ProbabilityBasics.Liggett
