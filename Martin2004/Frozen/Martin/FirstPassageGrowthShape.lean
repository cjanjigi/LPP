-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import Martin2004.Full.Martin.FirstPassageGrowthShape
public import LPP_Foundations.Frozen.Model.LastPassage
public import LPP_Foundations.Frozen.Model.Quadrant
public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import LPP_Foundations.Frozen.Model.FirstPassage
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal Pointwise

namespace LPPDifferentiability

/-- A6. Theorem 5.1(ii), d = 2, growth-set form (lines 1056-1065). Reading:
under (5.1) and (5.2) with d = 2, let h be the unique first-passage shape
function. If h(x) >= c ||x|| for some c > 0 (the source's condition
inf h(x)/||x|| > 0), then almost surely, for every epsilon > 0 and all large
t, (1 - epsilon) C is inside C(t)/t, which is inside (1 + epsilon) C, where
C(t) = {x : S(floor x) <= t} and C = {x : h(x) <= 1}. -/
theorem martin_first_passage_growth_shape
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : (∫⁻ t in Iio (0 : ℝ), (μ (Iic t)) ^ (1 / 2 : ℝ)) < ∞)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞) :
    ∃! h : Quadrant → ℝ,
      Continuous h ∧
      (∀ (c : ℝ≥0) (x : Quadrant),
        h (c * x.1, c * x.2) = (c : ℝ) * h x) ∧
      (∀ (x y : Quadrant) (a b : ℝ≥0), a + b = 1 →
        h (a * x.1 + b * y.1, a * x.2 + b * y.2) ≤
          (a : ℝ) * h x + (b : ℝ) * h y) ∧
      (∀ᵐ ω ∂environmentLaw μ,
        ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ z : ℕ × ℕ,
          N ≤ z.1 + z.2 →
          |firstPassage ω (0, 0) z - h ((z.1 : ℝ≥0), (z.2 : ℝ≥0))| ≤
            ε * ((z.1 + z.2 : ℕ) : ℝ)) ∧
      ((∃ c : ℝ, 0 < c ∧ ∀ x : Quadrant, c * ((x.1 : ℝ) + x.2) ≤ h x) →
        ∀ᵐ ω ∂environmentLaw μ, ∀ ε : ℝ≥0, 0 < ε → ∃ t₀ : ℝ≥0, ∀ t : ℝ≥0, t₀ ≤ t →
          (1 - ε) • {x : Quadrant | h x ≤ 1} ⊆
              t⁻¹ • {x : Quadrant | firstPassage ω 0 (⌊x.1⌋₊, ⌊x.2⌋₊) ≤ (t : ℝ)} ∧
            t⁻¹ • {x : Quadrant | firstPassage ω 0 (⌊x.1⌋₊, ⌊x.2⌋₊) ≤ (t : ℝ)} ⊆
              (1 + ε) • {x : Quadrant | h x ≤ 1}) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact LPPDifferentiability.Full.martin_first_passage_growth_shape μ hneg hpos
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end LPPDifferentiability
-- FROZEN_ANCHOR_SUFFIX_END
