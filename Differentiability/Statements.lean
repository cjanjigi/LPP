/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Statements.ShapeDefinitions
public import Martin2004.Statements.ShapeFacts
public import Differentiability.Frozen.Main.Differentiability

/-!
# The differentiability theorem, in two versions

Theorem 2.1 of the differentiability preprint: for an i.i.d. environment whose weight law `μ` is not
a point mass, has a finite moment of some order above `1` for the negative part and of some order
above `4` for the positive part, the shape function of last-passage percolation exists, is unique,
and is differentiable at every point of the open quadrant.

* Version A (`literal_shape_exists_unique_and_differentiable`): the statement
  `LPPDifferentiability.exists_unique_shape_differentiable_full` of the `Frozen` folder, copied
  verbatim (the only change is a leading underscore on the names of hypotheses that the statement
  does not use, to keep the unused-variable linter quiet).
* Version B (`plain_shape_exists_unique_and_differentiable`): the statement in the form of the
  paper, written with the named definitions of `ShapeDefinitions`: there is exactly one shape
  function, and it is differentiable.
* `plain_shape_exists_unique_and_differentiable_iff_literal`: the two versions are equivalent.
* `shape_exists_unique_and_differentiable`: version B with ordinary binders, with the label
  `Differentiability.theorem_2_1` as an alias.

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

/-- Version A of Theorem 2.1 of the differentiability preprint: the statement
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

/-- The theorem of the `Frozen` folder proves version A. -/
theorem literal_shape_exists_unique_and_differentiable_holds :
    literal_shape_exists_unique_and_differentiable :=
  LPPDifferentiability.exists_unique_shape_differentiable_full

/-- Version B of Theorem 2.1 of the differentiability preprint, in plain language and in the form
of the paper: if the weight law is not a point mass (assumption A1), the negative part has a finite
moment above order `1` (A2) and the positive part has a finite moment above order `4` (A3), then
there is exactly one shape function, and it is differentiable on the open quadrant. -/
def plain_shape_exists_unique_and_differentiable : Prop :=
  ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
    NotAPointMass μ → HasNegativePartMomentAbove μ 1 → HasPositivePartMomentAbove μ 4 →
      (∃! g : Quadrant → ℝ, IsShapeFunction μ g) ∧
        ∀ g : Quadrant → ℝ, IsShapeFunction μ g → DifferentiableOnOpenQuadrant g

/-- Versions A and B state the same thing. Version A asks for exactly one function that is a shape
function and is differentiable; shape functions are unique on their own (`isShapeFunction_unique`),
so this is the same as exactly one shape function, all of whose members are differentiable. The
named shape function is a block of four clauses in front of the differentiability clause, so the
proof also reassociates the conjunction. -/
theorem plain_shape_exists_unique_and_differentiable_iff_literal :
    plain_shape_exists_unique_and_differentiable ↔
      literal_shape_exists_unique_and_differentiable := by
  constructor
  · intro h μ _ hμ hneg hpos
    exact (shapeFunction_form_iff μ _).mp (h μ hμ hneg hpos)
  · intro h μ _ hμ hneg hpos
    exact (shapeFunction_form_iff μ _).mpr (h μ hμ hneg hpos)

/-- Differentiability paper, Theorem 2.1 (`thm:main`).

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

/-- The paper label of `shape_exists_unique_and_differentiable`. -/
alias theorem_2_1 := shape_exists_unique_and_differentiable

end LPPStatements.Differentiability
