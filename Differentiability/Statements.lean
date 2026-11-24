/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Statements.ShapeDefinitions
public import Martin2004.Statements.ShapeFacts
public import Differentiability.Frozen.Main.Differentiability
public import Differentiability.Paper.MainProof

/-!
# The main theorem of the differentiability paper

The paper supplies the shape function of last-passage percolation by Martin's shape theorem.
Theorem 2.1 (`thm:main`) then proves that this shape function is differentiable at every point
of the relative interior of the unit segment, equivalently throughout the open quadrant.

* `shape_differentiable_on_unit_segment` states Theorem 2.1 for a supplied shape.
* `LPPDifferentiability.Paper.differentiable_on_unit_segment_iff_open_quadrant` states the
  equivalence by homogeneity.
* `shape_exists_unique_and_differentiable` combines Martin's shape theorem with Theorem 2.1.
  `theorem_2_1` is its existing alias. The joint result is available in equivalent literal and
  named forms for the frozen and comparator interfaces.

## References

* C. Janjigian, F. Rassoul-Agha and T. Seppäläinen, *Differentiability of the shape function in the
  planar corner growth model*, preprint, Theorem 2.1.
* J. B. Martin, Limiting shape for directed percolation models, Ann. Probab. 32 (2004), Theorem 5.1
  and Remark 5.1(ii).
-/

@[expose] public section

open LPPDifferentiability MeasureTheory Filter Set Asymptotics
open scoped NNReal ENNReal Topology Pointwise

namespace LPPStatements.Differentiability

/-- Theorem 2.1 (`thm:main`) of the differentiability paper for a supplied last-passage shape. -/
alias shape_differentiable_on_unit_segment :=
  LPPDifferentiability.Paper.shape_differentiable_on_unit_segment

/-- The literal form of the joint shape and differentiability theorem. This is the statement
`LPPDifferentiability.exists_unique_shape_differentiable_full` of the `Frozen` folder, as a
proposition, with no named definitions. -/
def literal_shape_exists_unique_and_differentiable : Prop :=
  ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (_hnondegenerate : ∀ c : ℝ, μ ({c} : Set ℝ) < 1)
    (_hneg : ∃ pneg : ℝ, 1 < pneg ∧
      (∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ pneg) ∂μ) < ∞)
    (_hpos : ∃ ppos : ℝ, 4 < ppos ∧
      (∫⁻ t, ENNReal.ofReal ((max t 0) ^ ppos) ∂μ) < ∞),
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
      (∀ x : ℝ × ℝ, 0 < x.1 → 0 < x.2 →
        DifferentiableAt ℝ (quadrantExtension g) x)

/-- The frozen theorem proves the literal joint shape and differentiability statement. -/
theorem literal_shape_exists_unique_and_differentiable_holds :
    literal_shape_exists_unique_and_differentiable :=
  LPPDifferentiability.exists_unique_shape_differentiable_full

/-- The joint shape and differentiability statement using the named shape predicate. Under
(A1)–(A3) there is exactly one shape function and it is differentiable on the open quadrant. -/
def plain_shape_exists_unique_and_differentiable : Prop :=
  ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
    NotAPointMass μ → HasNegativePartMomentAbove μ 1 → HasPositivePartMomentAbove μ 4 →
      (∃! g : Quadrant → ℝ, IsShapeFunction μ g) ∧
        ∀ g : Quadrant → ℝ, IsShapeFunction μ g → DifferentiableOnOpenQuadrant g

/-- The named and literal joint statements are equivalent by uniqueness of the shape function.
The named shape predicate collects the four clauses that precede differentiability in the
literal statement. -/
theorem plain_shape_exists_unique_and_differentiable_iff_literal :
    plain_shape_exists_unique_and_differentiable ↔
      literal_shape_exists_unique_and_differentiable := by
  constructor
  · intro h μ _ hμ hneg hpos
    exact (shapeFunction_form_iff μ _).mp (h μ hμ hneg hpos)
  · intro h μ _ hμ hneg hpos
    exact (shapeFunction_form_iff μ _).mpr (h μ hμ hneg hpos)

/-- The shape theorem and Theorem 2.1 (`thm:main`) of the differentiability paper, combined.

Let `μ` be the law of i.i.d. real site weights, not a point mass (A1), with `E[(w⁻)^q] < ∞` for
some `q > 1` (A2) and `E[(w⁺)^q] < ∞` for some `q > 4` (A3). Then the shape function exists and is
unique, and it is differentiable at every point of the open quadrant. Here a shape function is a
function `g` that is continuous, homogeneous, concave, and approximates the last-passage time
uniformly almost surely.

The preprint states the differentiability of the shape function and cites the shape theorem from
Martin (2004), Theorem 5.1 and Remark 5.1(ii); the formal statement joins the two. -/
theorem shape_exists_unique_and_differentiable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : NotAPointMass μ) (hneg : HasNegativePartMomentAbove μ 1)
    (hpos : HasPositivePartMomentAbove μ 4) :
    (∃! g : Quadrant → ℝ, IsShapeFunction μ g) ∧
      ∀ g : Quadrant → ℝ, IsShapeFunction μ g → DifferentiableOnOpenQuadrant g :=
  plain_shape_exists_unique_and_differentiable_iff_literal.mpr
    literal_shape_exists_unique_and_differentiable_holds μ hμ hneg hpos

/-- The existing alias for the combined shape theorem and Theorem 2.1 (`thm:main`). -/
alias theorem_2_1 := shape_exists_unique_and_differentiable

end LPPStatements.Differentiability
