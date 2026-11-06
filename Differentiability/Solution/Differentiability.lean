/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Statements

/-!
# Solution: differentiability of the shape function

Proves `LPPAudit.Differentiability.shape_exists_unique_and_differentiable` of the challenge file from
the library. The definitions and the statement are the same as in the challenge file, character for
character.

The proof has two parts. First, for every definition, a theorem `<name>_eq` shows that it is the
library definition it copies: an equality (`rfl`) wherever the two texts agree. The model needs more
than `rfl`, because the challenge's paths form a new structure `Path` and its last-passage time is a
supremum over them, while the library takes the maximum of a finite image of its own paths. The
theorem `Path_equiv` gives a bijection between the two kinds of paths that preserves weights, and
`lastPassage_eq` uses it, together with the facts that there are finitely many paths and at least one,
to show that the supremum is the library's maximum. These theorems state facts about definitions
only. Second, the main theorem follows from the library statement
`LPPStatements.Differentiability.shape_exists_unique_and_differentiable`, which proves the same paper statement.
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

/-! ### Each definition above is the library definition it copies -/

/-- The challenge definition agrees with its library counterpart. -/
theorem Lattice_eq : Lattice = LPPDifferentiability.Lattice := rfl

/-- The challenge definition agrees with its library counterpart. -/
theorem Environment_eq : Environment = LPPDifferentiability.Environment := rfl

/-- The challenge definition agrees with its library counterpart. -/
theorem Quadrant_eq : Quadrant = LPPDifferentiability.Quadrant := rfl

/-- The challenge definition agrees with its library counterpart. -/
theorem environmentLaw_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    environmentLaw μ = LPPDifferentiability.environmentLaw μ := rfl

/-- The challenge's paths and the library's paths correspond one to one, and the correspondence
keeps the weight of every path. -/
theorem Path_equiv (u : Lattice) (d : ℕ × ℕ) :
    ∃ e : Path u d ≃ LPPDifferentiability.Path u d, ∀ (ω : Environment) (p : Path u d),
      pathWeight ω p = LPPDifferentiability.pathWeight ω (e p) :=
  ⟨{ toFun := fun p => ⟨p.vertex, p.start, p.finish, p.step⟩
     invFun := fun p => ⟨p.vertex, p.start, p.finish, p.step⟩
     left_inv := fun _ => rfl
     right_inv := fun _ => rfl }, fun _ _ => rfl⟩

/-- The last-passage time of the challenge, a supremum over paths, is the library's last-passage
time, the maximum of the weights of the finitely many paths. -/
theorem lastPassage_eq (ω : Environment) (u : Lattice) (d : ℕ × ℕ) :
    lastPassage ω u d = LPPDifferentiability.lastPassage ω u d := by
  classical
  obtain ⟨e, he⟩ := Path_equiv u d
  have hsup : lastPassage ω u d =
      ⨆ q : LPPDifferentiability.Path u d, LPPDifferentiability.pathWeight ω q :=
    (iSup_congr fun p => he ω p).trans (e.iSup_comp (g := LPPDifferentiability.pathWeight ω))
  rw [hsup]
  unfold LPPDifferentiability.lastPassage
  apply le_antisymm
  · refine ciSup_le fun q => Finset.le_max' _ _ ?_
    exact Finset.mem_image.mpr ⟨q, Finset.mem_univ q, rfl⟩
  · refine Finset.max'_le _ _ _ fun y hy => ?_
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hy
    exact le_ciSup (Set.finite_range _).bddAbove q

/-- The challenge definition agrees with its library counterpart. -/
theorem toQuadrant_eq (x : ℝ × ℝ) : toQuadrant x = LPPDifferentiability.toQuadrant x := rfl

/-- The challenge definition agrees with its library counterpart. -/
theorem quadrantExtension_eq (g : Quadrant → ℝ) :
    quadrantExtension g = LPPDifferentiability.quadrantExtension g := rfl

/-- The challenge definition agrees with its library counterpart. -/
theorem NotAPointMass_eq (μ : Measure ℝ) :
    NotAPointMass μ = LPPStatements.NotAPointMass μ := rfl

/-- The challenge definition agrees with its library counterpart. -/
theorem HasNegativePartMomentAbove_eq (μ : Measure ℝ) (p : ℝ) :
    HasNegativePartMomentAbove μ p = LPPStatements.HasNegativePartMomentAbove μ p := rfl

/-- The challenge definition agrees with its library counterpart. -/
theorem HasPositivePartMomentAbove_eq (μ : Measure ℝ) (p : ℝ) :
    HasPositivePartMomentAbove μ p = LPPStatements.HasPositivePartMomentAbove μ p := rfl

/-- The challenge definition agrees with its library counterpart. -/
theorem IsHomogeneous_eq (g : Quadrant → ℝ) :
    IsHomogeneous g = LPPStatements.IsHomogeneous g := rfl

/-- The challenge definition agrees with its library counterpart. -/
theorem IsConcaveOnQuadrant_eq (g : Quadrant → ℝ) :
    IsConcaveOnQuadrant g = LPPStatements.IsConcaveOnQuadrant g := rfl

/-- The challenge definition agrees with its library counterpart. -/
theorem ApproximatesLastPassage_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] (g : Quadrant → ℝ) :
    ApproximatesLastPassage μ g = LPPStatements.ApproximatesLastPassage μ g := by
  have h : lastPassage = LPPDifferentiability.lastPassage :=
    funext fun ω => funext fun u => funext fun d => lastPassage_eq ω u d
  unfold ApproximatesLastPassage LPPStatements.ApproximatesLastPassage
  rw [h]
  rfl

/-- The challenge definition agrees with its library counterpart. -/
theorem IsShapeFunction_iff (μ : Measure ℝ) [IsProbabilityMeasure μ] (g : Quadrant → ℝ) :
    IsShapeFunction μ g ↔ LPPStatements.IsShapeFunction μ g := by
  unfold IsShapeFunction LPPStatements.IsShapeFunction
  rw [ApproximatesLastPassage_eq]
  rfl

/-- The challenge definition agrees with its library counterpart. -/
theorem DifferentiableOnOpenQuadrant_eq (g : Quadrant → ℝ) :
    DifferentiableOnOpenQuadrant g = LPPStatements.DifferentiableOnOpenQuadrant g := rfl

/-! ### The main theorem -/

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
  obtain ⟨⟨g, hg, hunique⟩, hdifferentiable⟩ :=
    LPPStatements.Differentiability.shape_exists_unique_and_differentiable μ hμ hneg hpos
  exact ⟨⟨g, (IsShapeFunction_iff μ g).mpr hg,
      fun y hy => hunique y ((IsShapeFunction_iff μ y).mp hy)⟩,
    fun y hy => hdifferentiable y ((IsShapeFunction_iff μ y).mp hy)⟩

end LPPAudit.Differentiability
