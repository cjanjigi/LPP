module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

open MeasureTheory

namespace ProbabilityBasics.Liggett

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Liggett (1.3), Kingman's moment condition: for each `n ≥ 1`,
`E|X_{0,n}| < ∞`, and one constant `c` has `E X_{0,n} ≥ -c n` for all `n ≥ 1`. -/
def LiggettMomentCondition (μ : Measure Ω) (X : ℕ → ℕ → Ω → ℝ) : Prop :=
  (∀ n : ℕ, 0 < n → Integrable (X 0 n) μ) ∧
    ∃ c : ℝ, ∀ n : ℕ, 0 < n → -(c * n) ≤ ∫ ω, X 0 n ω ∂μ

end ProbabilityBasics.Liggett
