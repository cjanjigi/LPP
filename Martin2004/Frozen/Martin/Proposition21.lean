-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import Martin2004.Full.Martin.Proposition21
public import LPP_Foundations.Frozen.Model.LastPassage
public import LPP_Foundations.Frozen.Model.Quadrant
public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

@[expose] public section

open MeasureTheory Filter
open scoped NNReal Topology

namespace LPPDifferentiability

/-- A0. Proposition 2.1 in its literal generality, d = 2 (lines 177-184).
Reading: if the weight has a finite mean, there is exactly one extended-real
function g on the closed quadrant such that, in every real direction x, the
normalized expected passage time E T(floor(n x))/n and, almost surely, the
normalized passage time T(floor(n x))/n converge to g(x); the convergence also
holds in L1 whenever g(x) is finite; g is positively homogeneous, symmetric
in the two coordinates and superadditive. The value +infinity is allowed.
FLAG: the source proof ("immediate" from Kingman, line 174) does not treat
non-lattice directions with signed weights; see INVENTORY.md, S18. -/
theorem martin_prop_2_1
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ) :
    ∃! g : Quadrant → EReal,
      (∀ x : Quadrant, Tendsto (fun n : ℕ =>
        (((∫ ω : Environment, lastPassage ω 0
          (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
          ∂environmentLaw μ) / (n : ℝ) : ℝ) : EReal)) atTop (𝓝 (g x))) ∧
      (∀ x : Quadrant, ∀ᵐ ω ∂environmentLaw μ, Tendsto (fun n : ℕ =>
        ((lastPassage ω 0 (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) /
          (n : ℝ) : ℝ) : EReal)) atTop (𝓝 (g x))) ∧
      (∀ x : Quadrant, g x ≠ ⊤ → Tendsto (fun n : ℕ => ∫ ω : Environment,
        |lastPassage ω 0 (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) /
          (n : ℝ) - (g x).toReal| ∂environmentLaw μ) atTop (𝓝 0)) ∧
      (∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = ((c : ℝ) : EReal) * g x) ∧
      (∀ x : Quadrant, g (x.2, x.1) = g x) ∧
      (∀ x y : Quadrant, g x + g y ≤ g (x.1 + y.1, x.2 + y.2)) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact LPPDifferentiability.Full.martin_prop_2_1 μ hμ
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end LPPDifferentiability
-- FROZEN_ANCHOR_SUFFIX_END
