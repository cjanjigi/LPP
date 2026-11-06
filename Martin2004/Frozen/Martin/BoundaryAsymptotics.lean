-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import Martin2004.Full.Martin.BoundaryAsymptotics
public import LPP_Foundations.Frozen.Model.LastPassage
public import LPP_Foundations.Frozen.Model.Quadrant
public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Asymptotics.Defs

@[expose] public section

open MeasureTheory Filter Set Asymptotics
open scoped NNReal ENNReal Topology

namespace LPPDifferentiability

/-- A2. Theorem 2.4 (lines 213-226). Reading: under the two integrated
square-root tail conditions (2.6) and (2.7), the weight has a finite second
moment, and the unique shape function g of `exists_unique_shape_martin`
satisfies g(1, a) = m + 2 s sqrt(a) + o(sqrt(a)) as a decreases to 0, where m
is the mean and s the standard deviation of the weight. -/
theorem martin_boundary_asymptotics
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : (∫⁻ t in Iio (0 : ℝ), (μ (Iic t)) ^ (1 / 2 : ℝ)) < ∞)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞) :
    Integrable (fun t : ℝ => t ^ 2) μ ∧
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
      (fun α : ℝ≥0 => g (1, α) - ((∫ t : ℝ, t ∂μ) +
          2 * Real.sqrt (∫ t : ℝ, (t - ∫ s : ℝ, s ∂μ) ^ 2 ∂μ) * Real.sqrt (α : ℝ)))
        =o[𝓝[>] (0 : ℝ≥0)] (fun α : ℝ≥0 => Real.sqrt (α : ℝ)) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact LPPDifferentiability.Full.martin_boundary_asymptotics μ hneg hpos
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end LPPDifferentiability
-- FROZEN_ANCHOR_SUFFIX_END
