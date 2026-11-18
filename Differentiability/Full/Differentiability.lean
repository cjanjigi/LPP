/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.GeneralOffFlatDifferentiability
public import Differentiability.Probability.FlatTopDifferentiability
public import Martin2004.Probability.WeakNegativeShape
public import Differentiability.Probability.TopIndicatorShape
public import ProbabilityBasics.Probability.PositiveMomentTail
public import Differentiability.Analysis.DirectionalAssembly
public import LPP_Foundations.Frozen.Model.LastPassage
public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import LPP_Foundations.Frozen.Model.Quadrant
public import LPP_Foundations.Statements.ShapeDefinitions
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The shape theorem and differentiability of the shape function

The theorem here is the proof of the statement `exists_unique_shape_differentiable_full` in
`Frozen/Main/Differentiability.lean`. The shape function exists and is unique by the shape
theorem. Differentiability on the segment `{(a, 1 - a)}` splits according to whether the shape
function of the top-weight indicators is below `1` (the general off-flat theorem) or equal to `1`
(the flat-segment theorem). Homogeneity then carries differentiability to the open quadrant.

## Main results

- `exists_unique_shape_differentiable`: the shape function exists, is unique, and is differentiable
  at every point of the open quadrant.

## References

- C. Janjigian, F. Rassoul-Agha and T. Seppäläinen, *Differentiability of the shape function in the
  planar corner growth model*, preprint: the shape theorem (2.3), Theorem 2.1 with the remark after
  it, Section 2.3 (the flat segment) and Section 6.5 (the proof of Theorem 2.1).
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace LPPDifferentiability.Full

/-- **The shape theorem and Theorem 2.1 together.** Under (A1) (no point mass), (A2) (a
negative-part moment of order above one) and (A3) (a positive-part moment of order above
four), there is exactly one function `g` on the closed quadrant that is continuous,
positively homogeneous and concave and is the almost-sure uniform limit of the scaled
last-passage times, and its quadrant extension is differentiable at every point of the open
quadrant (the shape theorem (2.3) and Theorem 2.1 of the differentiability preprint). -/
theorem exists_unique_shape_differentiable
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hnondegenerate : LPPStatements.NotAPointMass μ)
    (hneg : LPPStatements.HasNegativePartMomentAbove μ 1)
    (hpos : LPPStatements.HasPositivePartMomentAbove μ 4) :
    ∃! g : Quadrant → ℝ,
      Continuous g ∧
      LPPStatements.IsHomogeneous g ∧
      LPPStatements.IsConcaveOnQuadrant g ∧
      LPPStatements.ApproximatesLastPassage μ g ∧
      LPPStatements.DifferentiableOnOpenQuadrant g := by
  -- Step 1 (assumption (A3)): the p > 4 moment gives the integrated square-root tail.
  have hsqrt : LPPStatements.HasSqrtUpperTail μ :=
    positive_integrated_sqrt_tail_lt_top_of_full_positive_moment μ hpos
  -- Step 2 (shape theorem (2.3)): the unique shape, with the `1 ≤ N` limit clause.
  obtain ⟨g, ⟨hgcont, hghom, hgconc, hgshape⟩, hguniq⟩ :=
    exists_unique_shape_of_negative_moment_and_positive_tail μ hneg hsqrt
  -- Steps 3-6 (Theorem 2.1 on the segment): the flat / off-flat dichotomy at `(a, 1 - a)`.
  have hseg : ∀ a : ℝ, 0 < a → a < 1 →
      DifferentiableAt ℝ (quadrantExtension g) (a, 1 - a) := by
    intro a ha₀ ha₁
    -- Step 3: the top-indicator shape `gtop` and its expected limit at the direction.
    obtain ⟨gtop, -, -, -, -, htlim, -, htbound, -, -, -⟩ :=
      exists_source_top_indicator_shape μ
    have hq₁ : ((toQuadrant (a, 1 - a)).1 : ℝ) = a := Real.coe_toNNReal a ha₀.le
    have hq₂ : ((toQuadrant (a, 1 - a)).2 : ℝ) = 1 - a :=
      Real.coe_toNNReal (1 - a) (by linarith)
    have htop := htlim (toQuadrant (a, 1 - a))
    rw [hq₁, hq₂] at htop
    -- Step 4: `gtop ≤ 1` on the segment (Section 2.3), then split.
    have hle : gtop (toQuadrant (a, 1 - a)) ≤ 1 := by
      have h := (htbound (toQuadrant (a, 1 - a))).2
      rw [hq₁, hq₂] at h
      linarith
    rcases hle.lt_or_eq with hlt | heq
    · -- Step 5: off the flat segment, the general theorem (Section 6.5).
      exact differentiableAt_of_off_flat_general μ hneg hpos g hgcont hghom hgconc hgshape
        a ha₀ ha₁ _ htop hlt
    · -- Step 6: on the flat segment, the flat-segment theorem (Section 2.3).
      rw [heq] at htop
      exact differentiableAt_of_top_flat μ hnondegenerate hneg g hgcont hghom hgconc hgshape
        a ha₀ ha₁ htop
  -- Step 7 (homogeneity, the remark after Theorem 2.1): from the segment to the open quadrant.
  refine ⟨g, ⟨hgcont, hghom, hgconc, ?_,
    differentiableAt_quadrantExtension_of_segment g hghom hseg⟩, ?_⟩
  · exact (LPPStatements.approximatesLastPassage_iff_positive_threshold μ g).mpr hgshape
  · rintro f ⟨hfcont, hfhom, hfconc, hfshape, -⟩
    exact hguniq f ⟨hfcont, hfhom, hfconc,
      (LPPStatements.approximatesLastPassage_iff_positive_threshold μ f).mp hfshape⟩

end LPPDifferentiability.Full
