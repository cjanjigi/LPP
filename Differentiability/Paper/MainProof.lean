/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Paper.Setting
import Differentiability.Probability.FlatTopDifferentiability
import Differentiability.Probability.GeneralOffFlatDifferentiability
import Differentiability.Probability.TopIndicatorShape
import Mathlib.Tactic.Linarith

/-! # Proof of the main theorem

The top-indicator shape is at most `1` on the unit segment. The directions at which it equals
`1` are handled by the flat-segment argument. At the others the disjoint-witness argument excludes
a corner. Both arguments apply to the shape supplied by the shape theorem.
-/

public section

open LPPStatements MeasureTheory
open scoped NNReal

namespace LPPDifferentiability.Paper

/-- Theorem `thm:main` of the differentiability paper. Under (A1)–(A3), the last-passage shape
of the weight law `μ` is differentiable at every point of the relative interior of the unit
segment. The paper supplies `g` by the shape theorem before stating the differentiability result. -/
theorem shape_differentiable_on_unit_segment (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : NotAPointMass μ) (hneg : HasNegativePartMomentAbove μ 1)
    (hpos : HasPositivePartMomentAbove μ 4) (g : Quadrant → ℝ) (hg : IsShapeFunction μ g) :
    ∀ a : ℝ, 0 < a → a < 1 → DifferentiableAt ℝ (quadrantExtension g) (a, 1 - a) := by
  obtain ⟨hgcont, hghom, hgconc, hgshape⟩ := hg
  have hgshape' := (approximatesLastPassage_iff_positive_threshold μ g).mp hgshape
  obtain ⟨gtop, -, -, -, -, htlim, -, htbound, -, -, -⟩ := exists_source_top_indicator_shape μ
  intro a ha₀ ha₁
  have hq₁ : ((toQuadrant (a, 1 - a)).1 : ℝ) = a := Real.coe_toNNReal a ha₀.le
  have hq₂ : ((toQuadrant (a, 1 - a)).2 : ℝ) = 1 - a :=
    Real.coe_toNNReal (1 - a) (sub_pos.mpr ha₁).le
  have htop := htlim (toQuadrant (a, 1 - a))
  rw [hq₁, hq₂] at htop
  have hle : gtop (toQuadrant (a, 1 - a)) ≤ 1 := by
    have h := (htbound (toQuadrant (a, 1 - a))).2
    rw [hq₁, hq₂] at h
    linarith
  rcases hle.lt_or_eq with hlt | heq
  · exact differentiableAt_of_off_flat_general μ hneg hpos g hgcont hghom hgconc hgshape'
      a ha₀ ha₁ _ htop hlt
  · rw [heq] at htop
    exact differentiableAt_of_top_weight_count_rate_one μ hμ hneg g hgcont hghom hgconc hgshape'
      a ha₀ ha₁ htop

end LPPDifferentiability.Paper
