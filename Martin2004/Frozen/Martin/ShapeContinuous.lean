-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import Martin2004.Full.Martin.ShapeContinuous
public import LPP_Foundations.Frozen.Model.LastPassage
public import LPP_Foundations.Frozen.Model.Quadrant
public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace LPPDifferentiability

/-- A1. Propositions 2.1-2.2 and Theorem 2.3, d = 2, in the finite setting
(lines 177-207). Reading: if the weight has a finite mean and the positive
tail integral of sqrt(P(X > t)) is finite, there is exactly one real function
g on the closed quadrant such that E T(floor(n x))/n tends to g(x) in every
real direction; along every natural direction a the passage time T(n a)/n
converges to g(a) almost surely and in L1; g is homogeneous, symmetric and
superadditive; and g is continuous on the whole closed quadrant, boundary
included. -/
theorem martin_shape_continuous
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞) :
    ∃! g : Quadrant → ℝ,
      (∀ x : Quadrant, Tendsto (fun n : ℕ =>
        (∫ ω : Environment, lastPassage ω 0
          (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
          ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (g x))) ∧
      (∀ a : ℕ × ℕ, ∀ᵐ ω ∂environmentLaw μ, Tendsto
        (fun n : ℕ => lastPassage ω 0 (n • a) / (n : ℝ)) atTop
        (𝓝 (g ((a.1 : ℝ≥0), (a.2 : ℝ≥0))))) ∧
      (∀ a : ℕ × ℕ, Tendsto (fun n : ℕ => ∫ ω : Environment,
        |lastPassage ω 0 (n • a) / (n : ℝ) - g ((a.1 : ℝ≥0), (a.2 : ℝ≥0))|
          ∂environmentLaw μ) atTop (𝓝 0)) ∧
      (∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x) ∧
      (∀ x : Quadrant, g (x.2, x.1) = g x) ∧
      (∀ x y : Quadrant, g x + g y ≤ g (x.1 + y.1, x.2 + y.2)) ∧
      Continuous g :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact LPPDifferentiability.Full.martin_shape_continuous μ hμ hpos
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end LPPDifferentiability
-- FROZEN_ANCHOR_SUFFIX_END
