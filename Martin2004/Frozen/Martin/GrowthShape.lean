-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import Martin2004.Full.Martin.LastPassageGrowthShape
public import LPP_Foundations.Frozen.Model.LastPassage
public import LPP_Foundations.Frozen.Model.Quadrant
public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal Pointwise

namespace LPPDifferentiability

/-- A5. Theorem 5.1(i), d = 2, growth-set form (lines 1022-1055). Reading:
under (5.1) and (5.2) with d = 2, and a positive mean weight, let g be the
unique shape function. Almost surely, for every epsilon > 0 and all large
times t, the scaled limit set (1 - epsilon) B is inside B(t)/t, which is
inside (1 + epsilon) B. Here B(t) = {x : T(floor x) <= t} is the last-passage
growth set at time t and B = {x : g(x) <= 1}. Scalars are nonnegative reals,
so 1 - epsilon is truncated at 0. -/
theorem martin_last_passage_growth_shape
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : (∫⁻ t in Iio (0 : ℝ), (μ (Iic t)) ^ (1 / 2 : ℝ)) < ∞)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞)
    (hmean : 0 < ∫ t : ℝ, t ∂μ) :
    ∃! g : Quadrant → ℝ,
      Continuous g ∧
      (∀ (c : ℝ≥0) (x : Quadrant),
        g (c * x.1, c * x.2) = (c : ℝ) * g x) ∧
      (∀ (x y : Quadrant) (a b : ℝ≥0), a + b = 1 →
        (a : ℝ) * g x + (b : ℝ) * g y ≤
          g (a * x.1 + b * y.1, a * x.2 + b * y.2)) ∧
      (∀ᵐ ω ∂environmentLaw μ,
        ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ z : ℕ × ℕ,
          N ≤ z.1 + z.2 →
          |lastPassage ω (0, 0) z - g ((z.1 : ℝ≥0), (z.2 : ℝ≥0))| ≤
            ε * ((z.1 + z.2 : ℕ) : ℝ)) ∧
      (∀ᵐ ω ∂environmentLaw μ, ∀ ε : ℝ≥0, 0 < ε → ∃ t₀ : ℝ≥0, ∀ t : ℝ≥0, t₀ ≤ t →
        (1 - ε) • {x : Quadrant | g x ≤ 1} ⊆
            t⁻¹ • {x : Quadrant | lastPassage ω 0 (⌊x.1⌋₊, ⌊x.2⌋₊) ≤ (t : ℝ)} ∧
          t⁻¹ • {x : Quadrant | lastPassage ω 0 (⌊x.1⌋₊, ⌊x.2⌋₊) ≤ (t : ℝ)} ⊆
            (1 + ε) • {x : Quadrant | g x ≤ 1}) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact LPPDifferentiability.Full.martin_last_passage_growth_shape μ hneg hpos hmean
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end LPPDifferentiability
-- FROZEN_ANCHOR_SUFFIX_END
