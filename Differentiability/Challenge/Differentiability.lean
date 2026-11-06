/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# Challenge: differentiability of the shape function

This file states Theorem 2.1 of the differentiability preprint using only Mathlib. It contains the
statement, with its proof left open, and exactly the definitions the statement uses: the model of
last-passage percolation on the integer lattice (sites, environment, environment law, up-right
paths, path weight, last-passage time), the quadrant and the extension of a function on it to the
plane, the assumptions on the weight law, and the definition of a shape function. The solution file
proves the same statement from the library.

## Main results

- `shape_exists_unique_and_differentiable`: the differentiability preprint, Theorem 2.1.

## References

- C. Janjigian, F. Rassoul-Agha and T. Seppäläinen, "Differentiability of the shape function in the
  planar corner growth model", preprint.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace LPPAudit.Differentiability

/-! ### The model -/

/-- The sites of the model: the integer lattice `ℤ²`. -/
abbrev Lattice := ℤ × ℤ

/-- An environment: a real weight at every site of the lattice. -/
abbrev Environment := Lattice → ℝ

/-- The law of the environment: the weights at different sites are independent, and each has the law
`μ`. -/
noncomputable def environmentLaw (μ : Measure ℝ) [IsProbabilityMeasure μ] : Measure Environment :=
  Measure.infinitePi (fun _ : Lattice => μ)

/-- An up-right path from the site `u` to the site `u + d`, where `d = (d.1, d.2)` is a pair of
natural numbers. It is a list of `d.1 + d.2 + 1` sites that starts at `u`, ends at `u + d`, and moves
one step to the right or one step up at each step. -/
structure Path (u : Lattice) (d : ℕ × ℕ) where
  /-- The sites of the path, in order. -/
  vertex : Fin (d.1 + d.2 + 1) → Lattice
  /-- The path starts at `u`. -/
  start : vertex 0 = u
  /-- The path ends at `u + d`. -/
  finish : vertex (Fin.last (d.1 + d.2)) = u + ((d.1 : ℤ), (d.2 : ℤ))
  /-- Each step goes one site to the right or one site up. -/
  step : ∀ i : Fin (d.1 + d.2),
    vertex i.succ = vertex i.castSucc + (1, 0) ∨
    vertex i.succ = vertex i.castSucc + (0, 1)

/-- The weight of a path: the sum of the weights of its sites, except the last one. -/
noncomputable def pathWeight (ω : Environment) {u : Lattice} {d : ℕ × ℕ} (p : Path u d) : ℝ :=
  ∑ i : Fin (d.1 + d.2), ω (p.vertex i.castSucc)

/-- The last-passage time from `u` to `u + d`: the largest weight of a path from `u` to `u + d`,
written as a supremum over all such paths. There are finitely many such paths, and at least one, so
the supremum is a maximum. (For the supremum of real numbers over an unbounded or empty family, Mathlib
uses the value `0`; that never happens here.) -/
noncomputable def lastPassage (ω : Environment) (u : Lattice) (d : ℕ × ℕ) : ℝ :=
  ⨆ p : Path u d, pathWeight ω p

/-- The closed quadrant `[0, ∞)²`, where the shape function lives. -/
abbrev Quadrant := ℝ≥0 × ℝ≥0

/-- The point of the closed quadrant nearest to a point of the plane: both coordinates are replaced
by their nonnegative parts. -/
def toQuadrant (x : ℝ × ℝ) : Quadrant := (x.1.toNNReal, x.2.toNNReal)

/-- A function on the closed quadrant, extended to the whole plane by `toQuadrant`, so that
differentiability of it is the usual notion for functions on `ℝ × ℝ`. -/
def quadrantExtension (g : Quadrant → ℝ) (x : ℝ × ℝ) : ℝ := g (toQuadrant x)

/-! ### Assumptions on the weight law -/

/-- The weight law `μ` is not a point mass: no single value carries all of the probability.
Assumption (A1) of the preprint. -/
def NotAPointMass (μ : Measure ℝ) : Prop :=
  ∀ c : ℝ, μ ({c} : Set ℝ) < 1

/-- The negative part of the weight has a finite moment of some order `q > p`.
For `p = 1`: assumption (A2) of the preprint, `E[(w⁻)^q] < ∞` for some `q > 1`. -/
def HasNegativePartMomentAbove (μ : Measure ℝ) (p : ℝ) : Prop :=
  ∃ q : ℝ, p < q ∧ (∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ q) ∂μ) < ∞

/-- The positive part of the weight has a finite moment of some order `q > p`.
For `p = 4`: assumption (A3) of the preprint, `E[(w⁺)^q] < ∞` for some `q > 4`. -/
def HasPositivePartMomentAbove (μ : Measure ℝ) (p : ℝ) : Prop :=
  ∃ q : ℝ, p < q ∧ (∫⁻ t, ENNReal.ofReal ((max t 0) ^ q) ∂μ) < ∞

/-! ### The shape function -/

/-- `g` is positively homogeneous: `g (c x) = c g x` for every scalar `c ≥ 0`. -/
def IsHomogeneous (g : Quadrant → ℝ) : Prop :=
  ∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x

/-- `g` is concave on the quadrant: `a g x + b g y ≤ g (a x + b y)` for `a, b ≥ 0` with `a + b = 1`. -/
def IsConcaveOnQuadrant (g : Quadrant → ℝ) : Prop :=
  ∀ (x y : Quadrant) (a b : ℝ≥0), a + b = 1 →
    (a : ℝ) * g x + (b : ℝ) * g y ≤ g (a * x.1 + b * y.1, a * x.2 + b * y.2)

/-- `g` approximates the last-passage time uniformly, almost surely: for almost every environment `ω`
and every `ε > 0`, `|T(0, z) - g z| ≤ ε (z₁ + z₂)` for all lattice points `z` of the quadrant far
enough from the origin. -/
def ApproximatesLastPassage (μ : Measure ℝ) [IsProbabilityMeasure μ] (g : Quadrant → ℝ) : Prop :=
  ∀ᵐ ω ∂environmentLaw μ,
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ z : ℕ × ℕ,
      N ≤ z.1 + z.2 →
      |lastPassage ω (0, 0) z - g ((z.1 : ℝ≥0), (z.2 : ℝ≥0))| ≤
        ε * ((z.1 + z.2 : ℕ) : ℝ)

/-- `g` is a shape function of the weight law `μ`: continuous on the closed quadrant, positively
homogeneous, concave, and approximating the last-passage time uniformly almost surely. -/
def IsShapeFunction (μ : Measure ℝ) [IsProbabilityMeasure μ] (g : Quadrant → ℝ) : Prop :=
  Continuous g ∧ IsHomogeneous g ∧ IsConcaveOnQuadrant g ∧ ApproximatesLastPassage μ g

/-- `g` is differentiable at every point of the open quadrant `x₁ > 0, x₂ > 0`, after extending it
to the plane by `quadrantExtension`. -/
def DifferentiableOnOpenQuadrant (g : Quadrant → ℝ) : Prop :=
  ∀ x : ℝ × ℝ, 0 < x.1 → 0 < x.2 → DifferentiableAt ℝ (quadrantExtension g) x

/-- The differentiability preprint, Theorem 2.1.

Let `μ` be the law of i.i.d. real site weights, not a point mass (A1), with `E[(w⁻)^q] < ∞` for some
`q > 1` (A2) and `E[(w⁺)^q] < ∞` for some `q > 4` (A3). Then the shape function exists and is unique,
and it is differentiable at every point of the open quadrant. Here a shape function is a function
`g` that is continuous, homogeneous, concave, and approximates the last-passage time uniformly almost
surely. -/
theorem shape_exists_unique_and_differentiable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : NotAPointMass μ) (hneg : HasNegativePartMomentAbove μ 1)
    (hpos : HasPositivePartMomentAbove μ 4) :
    (∃! g : Quadrant → ℝ, IsShapeFunction μ g) ∧
      ∀ g : Quadrant → ℝ, IsShapeFunction μ g → DifferentiableOnOpenQuadrant g := by
  sorry

end LPPAudit.Differentiability
