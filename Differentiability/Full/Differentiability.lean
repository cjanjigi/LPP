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
import Differentiability.Paper.MainProof

/-!
# The shape theorem and differentiability of the shape function

The theorem here is the proof of the joint statement `exists_unique_shape_differentiable_full` in
`Frozen/Main/Differentiability.lean`. The shape theorem supplies the unique shape function.
`Paper.shape_differentiable_on_unit_segment` proves differentiability on the relative interior of
the unit segment, and homogeneity extends it to the open quadrant.

## Main results

- `exists_unique_shape_differentiable`: the shape function exists, is unique, and is differentiable
  at every point of the open quadrant.

## References

- C. Janjigian, F. Rassoul-Agha and T. Seppäläinen, *Differentiability of the shape function in the
  planar corner growth model*, preprint: the uniform shape approximation `eq:shape`,
  Theorem `thm:main`, the flat segment (`sec:flat`) and the proof of the main theorem
  (`sub:proofmain`).
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
quadrant (the uniform shape approximation `eq:shape` and Theorem `thm:main` of the
differentiability preprint). -/
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
  have hsqrt : LPPStatements.HasSqrtUpperTail μ :=
    positive_integrated_sqrt_tail_lt_top_of_full_positive_moment μ hpos
  obtain ⟨g, ⟨hgcont, hghom, hgconc, hgshape⟩, hguniq⟩ :=
    exists_unique_shape_of_negative_moment_and_positive_tail μ hneg hsqrt
  have hgshape' := (LPPStatements.approximatesLastPassage_iff_positive_threshold μ g).mpr hgshape
  have hseg := Paper.shape_differentiable_on_unit_segment μ hnondegenerate hneg hpos
    g ⟨hgcont, hghom, hgconc, hgshape'⟩
  have hdiff := (Paper.differentiable_on_unit_segment_iff_open_quadrant g hghom).mp hseg
  refine ⟨g, ⟨hgcont, hghom, hgconc, hgshape', hdiff⟩, ?_⟩
  rintro f ⟨hfcont, hfhom, hfconc, hfshape, -⟩
  exact hguniq f ⟨hfcont, hfhom, hfconc,
    (LPPStatements.approximatesLastPassage_iff_positive_threshold μ f).mp hfshape⟩

end LPPDifferentiability.Full
