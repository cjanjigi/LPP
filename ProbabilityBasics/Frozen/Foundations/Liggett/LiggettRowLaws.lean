module

public import Mathlib.Probability.IdentDistrib
public import Mathlib.Basic.Real.Basic

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityBasics.Liggett

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Liggett (1.8): for each `m ≥ 0`, `{X_{m+1,m+k+1}, k ≥ 1}` has the same
joint distributions as `{X_{m,m+k}, k ≥ 1}`. Sequence index `j` stands for
the source index `k = j + 1`. -/
def LiggettRowLaws (μ : Measure Ω) (X : ℕ → ℕ → Ω → ℝ) : Prop :=
  ∀ m : ℕ, IdentDistrib (fun ω (j : ℕ) => X (m + 1) (m + 1 + (j + 1)) ω)
    (fun ω (j : ℕ) => X m (m + (j + 1)) ω) μ μ

end ProbabilityBasics.Liggett
