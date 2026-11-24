/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Statements.ShapeDefinitions
import Differentiability.Analysis.DirectionalAssembly

/-! # Setting and main result

The shape lives on the closed quadrant. At an interior point, differentiation of
`quadrantExtension g` is ordinary differentiation in the plane. The relative interior of the
unit segment consists of the points `(a, 1 - a)` with `0 < a < 1`.
-/

public section

open LPPStatements

namespace LPPDifferentiability.Paper

/-- The equivalence in `thm:main` of the differentiability paper. For a homogeneous function,
differentiability at every point of the relative interior of the unit segment is equivalent to
differentiability throughout the open quadrant. -/
theorem differentiable_on_unit_segment_iff_open_quadrant (g : Quadrant → ℝ)
    (hhom : IsHomogeneous g) :
    (∀ a : ℝ, 0 < a → a < 1 → DifferentiableAt ℝ (quadrantExtension g) (a, 1 - a)) ↔
      DifferentiableOnOpenQuadrant g := by
  constructor
  · exact differentiableAt_quadrantExtension_of_segment g hhom
  · intro h a ha₀ ha₁
    exact h (a, 1 - a) ha₀ (sub_pos.mpr ha₁)

end LPPDifferentiability.Paper
