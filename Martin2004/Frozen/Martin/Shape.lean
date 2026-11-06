-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import LPP_Foundations.Frozen.Model.LastPassage
public import LPP_Foundations.Frozen.Model.Quadrant
public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import Martin2004.Shape.Martin
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

@[expose] public section

open scoped NNReal ENNReal
open MeasureTheory Set

namespace LPPDifferentiability

/-- Planar uniform passage-time shape result proved in Martin Section 5.3,
under both integrated square-root tail conditions. The weak negative-tail
improvement in Remark 5.1(ii) is a separate open task. This theorem is UNPROVED. -/
theorem exists_unique_shape_martin
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : (∫⁻ t in Iio (0 : ℝ), (μ (Iic t)) ^ (1 / 2 : ℝ)) < ∞)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞) :
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
            ε * ((z.1 + z.2 : ℕ) : ℝ)) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact LPPDifferentiability.Martin.exists_unique_shape μ hneg hpos
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end LPPDifferentiability
-- FROZEN_ANCHOR_SUFFIX_END
