/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Shape.FirstPassageShape
public import LPP_Foundations.Frozen.Model.LastPassage
public import LPP_Foundations.Frozen.Model.Quadrant
public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import LPP_Foundations.Frozen.Model.FirstPassage
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Continuity of the first-passage shape function

The theorem here is the proof of the statement `martin_first_passage_continuous` in
`Frozen/Martin/FirstPassage.lean` (Martin (2004), Corollary 2.5(i) for `d = 2`). With a finite
mean and a finite lower square-root tail integral, the first-passage time has a unique shape
function that is homogeneous, symmetric, subadditive and continuous on the closed quadrant.

## Main results

- `martin_first_passage_continuous`: existence, uniqueness and continuity of the first-passage
  shape function.

## References

- J. B. Martin, *Limiting shape for directed percolation models*, Ann. Probab. 32 (2004),
  Corollary 2.5(i).
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace LPPDifferentiability.Full

/-- Martin (2004), Corollary 2.5(i), `d = 2`: if the weight has a finite mean and the lower tail
integral of `√P(X ≤ t)` over `t < 0` is finite, there is exactly one real function `h` on the
closed quadrant such that `E S(⌊n x⌋)/n` tends to `h x` in every direction, where `S` is the
first-passage time; `h` is homogeneous, symmetric, subadditive and continuous on the closed
quadrant. The paper gives no proof beyond the sign change described after Theorem 2.4. -/
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
      Continuous h := by
  -- Corollary 2.5(i) follows from the sign change described after Theorem 2.4: the
  -- first-passage shape under a finite mean and the lower square-root tail is minus the
  -- last-passage shape of the negated law; see `Shape/FirstPassageShape.lean`.
  exact exists_unique_continuous_firstPassage_real_expected_rate_of_integrable_and_negative_tail
    μ hμ hneg

end LPPDifferentiability.Full
