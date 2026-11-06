-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import Martin2004.Full.Martin.FirstPassageContinuous
public import LPP_Foundations.Frozen.Model.LastPassage
public import LPP_Foundations.Frozen.Model.Quadrant
public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import LPP_Foundations.Frozen.Model.FirstPassage
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace LPPDifferentiability

/-- A3. Corollary 2.5(i), d = 2 (lines 246-249). Reading: if the weight has a
finite mean and the lower tail integral of sqrt(P(X <= t)) over t < 0 is
finite, there is exactly one real function h on the closed quadrant such that
E S(floor(n x))/n tends to h(x) in every direction, where S is the first-passage
time; h is homogeneous, symmetric, subadditive and continuous on the closed
quadrant. Source gives no proof (sign change, lines 228-233). -/
theorem martin_first_passage_continuous
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ)
    (hneg : (∫⁻ t in Iio (0 : ℝ), (μ (Iic t)) ^ (1 / 2 : ℝ)) < ∞) :
    ∃! h : Quadrant → ℝ,
      (∀ x : Quadrant, Tendsto (fun n : ℕ =>
        (∫ ω : Environment, firstPassage ω 0
          (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
          ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (h x))) ∧
      (∀ (c : ℝ≥0) (x : Quadrant), h (c * x.1, c * x.2) = (c : ℝ) * h x) ∧
      (∀ x : Quadrant, h (x.2, x.1) = h x) ∧
      (∀ x y : Quadrant, h (x.1 + y.1, x.2 + y.2) ≤ h x + h y) ∧
      Continuous h :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact LPPDifferentiability.Full.martin_first_passage_continuous μ hμ hneg
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end LPPDifferentiability
-- FROZEN_ANCHOR_SUFFIX_END
