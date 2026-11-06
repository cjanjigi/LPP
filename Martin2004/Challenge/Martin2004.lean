/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Scalar
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# Challenge: the limit shape of directed percolation (Martin 2004)

This file states the main results of Martin (2004), for the planar case `d = 2`, using only Mathlib.
It contains the statements, with their proofs left open, and exactly the definitions the statements
use, including its own copy of the percolation model (sites, weights, directed paths, last-passage
and first-passage times). The solution file proves the same statements from the library.

The file follows the paper's sections. The shape statements have the form of the paper: the shape
function exists and is unique, and it has the stated property.

## Main results

- `extendedShape_limits_of_finite_mean`: Martin (2004), Proposition 2.1.
- `shape_continuous_of_finite_mean`: Martin (2004), Propositions 2.1-2.2 and Theorem 2.3.
- `shape_function_exists_unique`: Martin (2004), Section 5.3.
- `shape_boundary_asymptotics`: Martin (2004), Theorem 2.4.
- `firstPassageShape_continuous`: Martin (2004), Corollary 2.5(i).
- `firstPassageShape_boundary_asymptotics`: Martin (2004), Corollary 2.5(ii).
- `lastPassage_growthSets_converge`: Martin (2004), Theorem 5.1(i).
- `firstPassage_growthSets_converge`: Martin (2004), Theorem 5.1(ii).
- `taxicab_lower_bound_of_subadditive`: Martin (2004), Remark 5.1(i).

## References

- J. B. Martin, "Limiting shape for directed percolation models", Ann. Probab. 32 (2004).
-/

@[expose] public section

open MeasureTheory Filter Set Asymptotics
open scoped NNReal ENNReal Topology Pointwise

namespace LPPAudit.Martin2004

/-! ### Section 2: the model -/

/-- The sites of the lattice: pairs of integers. -/
abbrev Lattice : Type := ℤ × ℤ

/-- An environment gives a real weight to every site. -/
abbrev Environment : Type := Lattice → ℝ

/-- The environment with independent weights, each with law `μ`. -/
noncomputable def environmentLaw (μ : Measure ℝ) [IsProbabilityMeasure μ] : Measure Environment :=
  Measure.infinitePi (fun _ : Lattice => μ)

/-- The closed positive quadrant `ℝ≥0 × ℝ≥0`. -/
abbrev Quadrant : Type := ℝ≥0 × ℝ≥0

/-- A directed path from `u` to `u + d`: a list of `d.1 + d.2 + 1` sites, starting at `u`, ending at
`u + d`, each step raising one coordinate by 1. -/
structure Path (u : Lattice) (d : ℕ × ℕ) where
  /-- The sites of the path, in order. -/
  vertex : Fin (d.1 + d.2 + 1) → Lattice
  /-- The first site is `u`. -/
  start : vertex 0 = u
  /-- The last site is `u + d`. -/
  finish : vertex (Fin.last (d.1 + d.2)) = u + ((d.1 : ℤ), (d.2 : ℤ))
  /-- Each step raises one coordinate by 1. -/
  step : ∀ i : Fin (d.1 + d.2),
    vertex i.succ = vertex i.castSucc + (1, 0) ∨
    vertex i.succ = vertex i.castSucc + (0, 1)

/-- The weight of a path: the sum of the weights of its sites, the final site left out (Martin's
convention for `Π[z₁, z₂)`). -/
noncomputable def pathWeight (ω : Environment) {u : Lattice} {d : ℕ × ℕ} (p : Path u d) : ℝ :=
  ∑ i : Fin (d.1 + d.2), ω (p.vertex i.castSucc)

/-- The last-passage time `T(u, u + d)` of Martin (2004), (2.1): the supremum of the path weights over
all directed paths from `u` to `u + d`. There are finitely many paths, and at least one, so this
supremum is a maximum. -/
noncomputable def lastPassage (ω : Environment) (u : Lattice) (d : ℕ × ℕ) : ℝ :=
  ⨆ p : Path u d, pathWeight ω p

/-- The first-passage time `S(u, u + d)` of Martin (2004), (2.9): the infimum of the path weights over
all directed paths from `u` to `u + d`. There are finitely many paths, and at least one, so this
infimum is a minimum. -/
noncomputable def firstPassage (ω : Environment) (u : Lattice) (d : ℕ × ℕ) : ℝ :=
  ⨅ p : Path u d, pathWeight ω p

/-! ### Section 2: conditions on the weight law -/

/-- The weight has a finite mean, `E |X| < ∞`: Martin (2004), condition (2.4). -/
def HasFiniteMean (μ : Measure ℝ) : Prop :=
  Integrable (fun t : ℝ => t) μ

/-- The weight has a finite second moment, so its variance `σ²` exists: the standing assumption of
Martin (2004), Theorem 2.4. -/
def HasFiniteSecondMoment (μ : Measure ℝ) : Prop :=
  Integrable (fun t : ℝ => t ^ 2) μ

/-- The upper tail of the weight is integrable in the square-root sense: `∫₀^∞ (1 - F(s))^(1/2) ds < ∞`,
where `1 - F(s) = μ (s, ∞)`. This is Martin (2004), condition (2.6), the case `d = 2` of (2.5) and
(5.2). -/
def HasSqrtUpperTail (μ : Measure ℝ) : Prop :=
  (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞

/-- The lower tail of the weight is integrable in the square-root sense: `∫_{-∞}^0 F(s)^(1/2) ds < ∞`,
where `F(s) = μ (-∞, s]`. This is Martin (2004), condition (2.7), the case `d = 2` of (5.1). -/
def HasSqrtLowerTail (μ : Measure ℝ) : Prop :=
  (∫⁻ t in Iio (0 : ℝ), (μ (Iic t)) ^ (1 / 2 : ℝ)) < ∞

/-- The mean `m = ∫ t dμ(t)` of the weight law (the `µ` of Martin (2004), Theorem 2.4). -/
noncomputable def weightMean (μ : Measure ℝ) : ℝ :=
  ∫ t : ℝ, t ∂μ

/-- The variance `σ² = ∫ (t - m)² dμ(t)` of the weight law (Martin (2004), Theorem 2.4). -/
noncomputable def weightVariance (μ : Measure ℝ) : ℝ :=
  ∫ t : ℝ, (t - weightMean μ) ^ 2 ∂μ

/-- The standard deviation `σ` of the weight law (Martin (2004), Theorem 2.4). -/
noncomputable def weightStdDev (μ : Measure ℝ) : ℝ :=
  Real.sqrt (weightVariance μ)

/-! ### Section 2: properties of a function on the closed quadrant -/

/-- `g` is positively homogeneous: `g (c x) = c g x` for every scalar `c ≥ 0`.
Martin (2004), Proposition 2.1(ii). -/
def IsHomogeneous (g : Quadrant → ℝ) : Prop :=
  ∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x

/-- `g` with values in the extended reals is positively homogeneous: `g (c x) = c g x` for every
`c ≥ 0`. Martin (2004), Proposition 2.1(ii), where `g x = +∞` is allowed; the product is Mathlib's
product in `EReal`, with the convention `0 * ⊤ = 0`. -/
def IsHomogeneousExtended (g : Quadrant → EReal) : Prop :=
  ∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = ((c : ℝ) : EReal) * g x

/-- `g` is symmetric in the two coordinates: `g (x₂, x₁) = g (x₁, x₂)`.
Martin (2004), Proposition 2.1(iii) with `d = 2`. -/
def IsSymmetric {M : Type*} (g : Quadrant → M) : Prop :=
  ∀ x : Quadrant, g (x.2, x.1) = g x

/-- `g` is superadditive: `g x + g y ≤ g (x + y)`. Martin (2004), Proposition 2.1(iv). For values in
the extended reals, the sum is Mathlib's addition in `EReal`, with the convention `⊤ + ⊥ = ⊥`. -/
def IsSuperadditive {M : Type*} [Add M] [LE M] (g : Quadrant → M) : Prop :=
  ∀ x y : Quadrant, g x + g y ≤ g (x.1 + y.1, x.2 + y.2)

/-- `h` is subadditive: `h (x + y) ≤ h x + h y`. The first-passage analogue of Martin (2004),
Proposition 2.1(iv), used in Remark 5.1(i). -/
def IsSubadditive {M : Type*} [Add M] [LE M] (h : Quadrant → M) : Prop :=
  ∀ x y : Quadrant, h (x.1 + y.1, x.2 + y.2) ≤ h x + h y

/-- `g` is concave on the quadrant, in the form `a g x + b g y ≤ g (a x + b y)` for `a, b ≥ 0` with
`a + b = 1`: the concavity of the set `B` of Martin (2004), Section 5.1. -/
def IsConcaveOnQuadrant (g : Quadrant → ℝ) : Prop :=
  ∀ (x y : Quadrant) (a b : ℝ≥0), a + b = 1 →
    (a : ℝ) * g x + (b : ℝ) * g y ≤ g (a * x.1 + b * y.1, a * x.2 + b * y.2)

/-- `h` is convex on the quadrant, in the form `h (a x + b y) ≤ a h x + b h y` for `a, b ≥ 0` with
`a + b = 1`: the convexity of the set `C` of Martin (2004), Section 5.1. -/
def IsConvexOnQuadrant (h : Quadrant → ℝ) : Prop :=
  ∀ (x y : Quadrant) (a b : ℝ≥0), a + b = 1 →
    h (a * x.1 + b * y.1, a * x.2 + b * y.2) ≤ (a : ℝ) * h x + (b : ℝ) * h y

/-- The taxicab norm `‖x‖ = x₁ + x₂` of a point of the closed quadrant: the norm of Martin (2004),
Section 2, for `d = 2`. -/
def taxicabNorm (x : Quadrant) : ℝ :=
  (x.1 : ℝ) + x.2

/-! ### Section 2: the limit of expected passage times and Proposition 2.1 -/

/-- `g` is the limit of the expected last-passage rates in every direction: for every `x` in the
closed quadrant, `E T(⌊n x⌋) / n → g x`. Martin (2004), (2.3) and Proposition 2.1. -/
def IsExpectedRateShape (μ : Measure ℝ) [IsProbabilityMeasure μ] (g : Quadrant → ℝ) : Prop :=
  ∀ x : Quadrant, Tendsto (fun n : ℕ =>
    (∫ ω : Environment, lastPassage ω 0
      (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
      ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (g x))

/-- `h` is the limit of the expected first-passage rates in every direction: for every `x` in the
closed quadrant, `E S(⌊n x⌋) / n → h x`. Martin (2004), (2.10) and Corollary 2.5. -/
def IsFirstPassageExpectedRateShape (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : Quadrant → ℝ) : Prop :=
  ∀ x : Quadrant, Tendsto (fun n : ℕ =>
    (∫ ω : Environment, firstPassage ω 0
      (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
      ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (h x))

/-- `g`, with values in the extended reals, is the limit of the expected last-passage rate in
every direction. Martin (2004), (2.3), with the value `+∞` allowed. -/
def IsExtendedExpectedRateShape (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (g : Quadrant → EReal) : Prop :=
  ∀ x : Quadrant, Tendsto (fun n : ℕ =>
    (((∫ ω : Environment, lastPassage ω 0
      (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
      ∂environmentLaw μ) / (n : ℝ) : ℝ) : EReal)) atTop (𝓝 (g x))

/-- `g`, with values in the extended reals, is the almost sure limit of the last-passage rate in
every real direction: `T(⌊n x⌋) / n → g x` almost surely. Martin (2004), Proposition 2.1(i). -/
def IsExtendedAlmostSureShape (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (g : Quadrant → EReal) : Prop :=
  ∀ x : Quadrant, ∀ᵐ ω ∂environmentLaw μ, Tendsto (fun n : ℕ =>
    ((lastPassage ω 0 (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) /
      (n : ℝ) : ℝ) : EReal)) atTop (𝓝 (g x))

/-- `g`, with values in the extended reals, is the `L¹` limit of the last-passage rate wherever it
is finite: if `g x ≠ +∞` then `E |T(⌊n x⌋) / n - g x| → 0`. Martin (2004), Proposition 2.1(i), the
bracketed clause. -/
def IsExtendedL1Shape (μ : Measure ℝ) [IsProbabilityMeasure μ] (g : Quadrant → EReal) : Prop :=
  ∀ x : Quadrant, g x ≠ ⊤ → Tendsto (fun n : ℕ => ∫ ω : Environment,
    |lastPassage ω 0 (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) /
      (n : ℝ) - (g x).toReal| ∂environmentLaw μ) atTop (𝓝 0)

/-- `g`, with values in the extended reals, has all the properties of Martin (2004), Proposition 2.1:
the expected rate, the almost sure limit, the `L¹` limit where finite, homogeneity, symmetry and
superadditivity. -/
def IsExtendedShape (μ : Measure ℝ) [IsProbabilityMeasure μ] (g : Quadrant → EReal) : Prop :=
  IsExtendedExpectedRateShape μ g ∧ IsExtendedAlmostSureShape μ g ∧ IsExtendedL1Shape μ g ∧
    IsHomogeneousExtended g ∧ IsSymmetric g ∧ IsSuperadditive g

/-- Martin (2004), Proposition 2.1.

If the weight has a finite mean, there is exactly one function `g` from the closed quadrant to the
extended reals with all the properties of `IsExtendedShape`: in every real direction `x`, the
normalized expected last-passage time `E T(⌊n x⌋) / n` and, almost surely, `T(⌊n x⌋) / n` converge to
`g x`; the convergence also holds in `L¹` wherever `g x` is finite; `g` is positively homogeneous,
symmetric and superadditive. The value `+∞` is allowed. This is the case `d = 2`. -/
theorem extendedShape_limits_of_finite_mean (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : HasFiniteMean μ) : ∃! g : Quadrant → EReal, IsExtendedShape μ g := by
  sorry

/-! ### Section 2: Propositions 2.1-2.2 and Theorem 2.3 -/

/-- Almost surely, along every lattice direction `a`, `T(n a) / n → g a` (convergence along the
multiples of a lattice point). Martin (2004), Proposition 2.1(i) for lattice directions. -/
def HasAlmostSureLatticeRate (μ : Measure ℝ) [IsProbabilityMeasure μ] (g : Quadrant → ℝ) :
    Prop :=
  ∀ a : ℕ × ℕ, ∀ᵐ ω ∂environmentLaw μ, Tendsto
    (fun n : ℕ => lastPassage ω 0 (n • a) / (n : ℝ)) atTop
    (𝓝 (g ((a.1 : ℝ≥0), (a.2 : ℝ≥0))))

/-- Along every lattice direction `a`, `T(n a) / n → g a` in `L¹`. Martin (2004),
Proposition 2.1(i), the `L¹` clause, for lattice directions with `g` finite. -/
def HasL1LatticeRate (μ : Measure ℝ) [IsProbabilityMeasure μ] (g : Quadrant → ℝ) : Prop :=
  ∀ a : ℕ × ℕ, Tendsto (fun n : ℕ => ∫ ω : Environment,
    |lastPassage ω 0 (n • a) / (n : ℝ) - g ((a.1 : ℝ≥0), (a.2 : ℝ≥0))|
      ∂environmentLaw μ) atTop (𝓝 0)

/-- `g` is a real-valued limit shape function in the sense of Martin (2004), Proposition 2.1: the
limit of the expected rate in every direction, the almost sure and `L¹` limit along lattice
directions, and homogeneous, symmetric and superadditive. Continuity is not included; it is the
content of Theorem 2.3. -/
def IsExpectedRateLimitFunction (μ : Measure ℝ) [IsProbabilityMeasure μ] (g : Quadrant → ℝ) :
    Prop :=
  IsExpectedRateShape μ g ∧ HasAlmostSureLatticeRate μ g ∧ HasL1LatticeRate μ g ∧
    IsHomogeneous g ∧ IsSymmetric g ∧ IsSuperadditive g

/-- Martin (2004), Propositions 2.1-2.2 and Theorem 2.3.

If the weight has a finite mean and satisfies the upper tail condition (2.6), the limit shape function
exists and is unique, and it is continuous. Here a limit shape function is a real function `g` on the
closed quadrant such that `E T(⌊n x⌋) / n → g x` in every real direction; along every lattice
direction `T(n a) / n → g a` almost surely and in `L¹`; and `g` is homogeneous, symmetric and
superadditive. The continuity holds on the whole closed quadrant, boundary included. This is the case
`d = 2`. -/
theorem shape_continuous_of_finite_mean (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : HasFiniteMean μ) (hpos : HasSqrtUpperTail μ) :
    (∃! g : Quadrant → ℝ, IsExpectedRateLimitFunction μ g) ∧
      ∀ g : Quadrant → ℝ, IsExpectedRateLimitFunction μ g → Continuous g := by
  sorry

/-! ### Section 5: shape functions of last-passage and first-passage percolation -/

/-- `g` approximates the last-passage time uniformly, almost surely: for almost every environment
`ω` and every `ε > 0`, `|T(0, z) - g z| ≤ ε ‖z‖` for all lattice points `z` far enough from the
origin. This is the content of Martin (2004), Theorem 5.1 before taking growth sets. -/
def ApproximatesLastPassage (μ : Measure ℝ) [IsProbabilityMeasure μ] (g : Quadrant → ℝ) :
    Prop :=
  ∀ᵐ ω ∂environmentLaw μ,
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ z : ℕ × ℕ,
      N ≤ z.1 + z.2 →
      |lastPassage ω (0, 0) z - g ((z.1 : ℝ≥0), (z.2 : ℝ≥0))| ≤
        ε * ((z.1 + z.2 : ℕ) : ℝ)

/-- `h` approximates the first-passage time uniformly, almost surely: for almost every environment
`ω` and every `ε > 0`, `|S(0, z) - h z| ≤ ε ‖z‖` for all lattice points `z` far enough from the
origin. The first-passage analogue of `ApproximatesLastPassage`; Martin (2004), Section 5.1. -/
def ApproximatesFirstPassage (μ : Measure ℝ) [IsProbabilityMeasure μ] (h : Quadrant → ℝ) :
    Prop :=
  ∀ᵐ ω ∂environmentLaw μ,
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ z : ℕ × ℕ,
      N ≤ z.1 + z.2 →
      |firstPassage ω (0, 0) z - h ((z.1 : ℝ≥0), (z.2 : ℝ≥0))| ≤
        ε * ((z.1 + z.2 : ℕ) : ℝ)

/-- `g` is a shape function of the weight law `μ` (last-passage percolation): continuous on the
closed quadrant, positively homogeneous, concave, and approximating the last-passage time
uniformly almost surely. This is the function `g` of Martin (2004), Section 2 and Theorem 5.1. -/
def IsShapeFunction (μ : Measure ℝ) [IsProbabilityMeasure μ] (g : Quadrant → ℝ) : Prop :=
  Continuous g ∧ IsHomogeneous g ∧ IsConcaveOnQuadrant g ∧ ApproximatesLastPassage μ g

/-- `h` is a shape function of the weight law `μ` for first-passage percolation: continuous on the
closed quadrant, positively homogeneous, convex, and approximating the first-passage time
uniformly almost surely. This is the function `h` of Martin (2004), (2.10), Corollary 2.5 and
Theorem 5.1(ii). -/
def IsFirstPassageShapeFunction (μ : Measure ℝ) [IsProbabilityMeasure μ] (h : Quadrant → ℝ) :
    Prop :=
  Continuous h ∧ IsHomogeneous h ∧ IsConvexOnQuadrant h ∧ ApproximatesFirstPassage μ h

/-! ### Section 5.3: the uniform shape statement -/

/-- Martin (2004), Section 5.3.

If the weight satisfies the tail conditions (2.7) and (2.6), there is exactly one continuous,
homogeneous, concave function `g` on the closed quadrant that approximates the last-passage time
`T(z)` within `ε ‖z‖` for all long `z`, almost surely. This is the uniform shape statement behind
Theorem 5.1, with Proposition 2.1 and Theorem 2.3, for `d = 2`. -/
theorem shape_function_exists_unique (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : HasSqrtLowerTail μ) (hpos : HasSqrtUpperTail μ) :
    ∃! g : Quadrant → ℝ, IsShapeFunction μ g := by
  sorry

/-! ### Section 2: Theorem 2.4 -/

/-- Martin (2004), (2.8): `g (1, α) = m + 2 s √α + o(√α)` as `α ↓ 0`, where `m` is the mean and
`s` the standard deviation of the weight. -/
def HasBoundaryAsymptotics (g : Quadrant → ℝ) (m s : ℝ) : Prop :=
  (fun α : ℝ≥0 => g (1, α) - (m + 2 * s * Real.sqrt (α : ℝ)))
    =o[𝓝[>] (0 : ℝ≥0)] (fun α : ℝ≥0 => Real.sqrt (α : ℝ))

/-- Martin (2004), Theorem 2.4.

Under the tail conditions (2.7) and (2.6), the weight has a finite second moment, and the shape function
exists and is unique, and it satisfies `g (1, α) = m + 2 s √α + o(√α)` as `α ↓ 0`, where `m` is the mean
and `s` the standard deviation of the weight. This is the case `d = 2`. -/
theorem shape_boundary_asymptotics (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : HasSqrtLowerTail μ) (hpos : HasSqrtUpperTail μ) :
    HasFiniteSecondMoment μ ∧
      (∃! g : Quadrant → ℝ, IsShapeFunction μ g) ∧
        ∀ g : Quadrant → ℝ, IsShapeFunction μ g →
          HasBoundaryAsymptotics g (weightMean μ) (weightStdDev μ) := by
  sorry

/-! ### Section 2: Corollary 2.5 -/

/-- `h` is a first-passage limit shape function in the sense of Martin (2004), (2.10) and
Corollary 2.5(i): the limit of the expected first-passage rate in every direction, homogeneous,
symmetric and subadditive. Continuity is not included; it is the content of Corollary 2.5(i). -/
def IsFirstPassageExpectedRateLimit (μ : Measure ℝ) [IsProbabilityMeasure μ] (h : Quadrant → ℝ) :
    Prop :=
  IsFirstPassageExpectedRateShape μ h ∧ IsHomogeneous h ∧ IsSymmetric h ∧ IsSubadditive h

/-- Martin (2004), Corollary 2.5(i).

If the weight has a finite mean and satisfies the lower tail condition (2.7), the first-passage limit
shape function exists and is unique, and it is continuous on the closed quadrant. Here a first-passage
limit shape function is a real function `h` on the closed quadrant such that `E S(⌊n x⌋) / n → h x` in
every direction, where `S` is the first-passage time, and `h` is homogeneous, symmetric and
subadditive. This is the case `d = 2`. -/
theorem firstPassageShape_continuous (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : HasFiniteMean μ) (hneg : HasSqrtLowerTail μ) :
    (∃! h : Quadrant → ℝ, IsFirstPassageExpectedRateLimit μ h) ∧
      ∀ h : Quadrant → ℝ, IsFirstPassageExpectedRateLimit μ h → Continuous h := by
  sorry

/-- Martin (2004), Corollary 2.5(ii): `h (1, α) = m - 2 s √α + o(√α)` as `α ↓ 0`, where `m` is the
mean and `s` the standard deviation of the weight. -/
def HasFirstPassageBoundaryAsymptotics (h : Quadrant → ℝ) (m s : ℝ) : Prop :=
  (fun α : ℝ≥0 => h (1, α) - (m - 2 * s * Real.sqrt (α : ℝ)))
    =o[𝓝[>] (0 : ℝ≥0)] (fun α : ℝ≥0 => Real.sqrt (α : ℝ))

/-- Martin (2004), Corollary 2.5(ii).

Under the tail conditions (2.7) and (2.6), the weight has a finite second moment, and the first-passage
shape function exists and is unique, and it satisfies `h (1, α) = m - 2 s √α + o(√α)` as `α ↓ 0`, where
`m` is the mean and `s` the standard deviation of the weight. Here a first-passage shape function is a
continuous, homogeneous, convex function `h` on the closed quadrant that approximates the first-passage
time `S(z)` within `ε ‖z‖` for all long `z`, almost surely. This is the case `d = 2`. -/
theorem firstPassageShape_boundary_asymptotics (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : HasSqrtLowerTail μ) (hpos : HasSqrtUpperTail μ) :
    HasFiniteSecondMoment μ ∧
      (∃! h : Quadrant → ℝ, IsFirstPassageShapeFunction μ h) ∧
        ∀ h : Quadrant → ℝ, IsFirstPassageShapeFunction μ h →
          HasFirstPassageBoundaryAsymptotics h (weightMean μ) (weightStdDev μ) := by
  sorry

/-! ### Section 5.1: growth sets and Theorem 5.1 -/

/-- The last-passage growth set at time `t`: `B(t) = {x : T(⌊x⌋) ≤ t}`, the points of the quadrant
reached by time `t`. Martin (2004), Section 5.1. -/
def lastPassageGrowthSet (ω : Environment) (t : ℝ) : Set Quadrant :=
  {x : Quadrant | lastPassage ω 0 (⌊x.1⌋₊, ⌊x.2⌋₊) ≤ t}

/-- The first-passage growth set at time `t`: `C(t) = {x : S(⌊x⌋) ≤ t}`. Martin (2004),
Section 5.1. -/
def firstPassageGrowthSet (ω : Environment) (t : ℝ) : Set Quadrant :=
  {x : Quadrant | firstPassage ω 0 (⌊x.1⌋₊, ⌊x.2⌋₊) ≤ t}

/-- The limit shape `{x : g x ≤ 1}` of a shape function: `B = {x : g x ≤ 1}` for last passage and
`C = {x : h x ≤ 1}` for first passage. Martin (2004), Section 5.1. -/
def shapeSublevelSet (g : Quadrant → ℝ) : Set Quadrant :=
  {x : Quadrant | g x ≤ 1}

/-- The growth sets `growth t`, rescaled by `1/t`, converge to the shape `B`: for every `ε > 0` and
all large `t`, `(1 - ε) B ⊆ growth t / t ⊆ (1 + ε) B`. Martin (2004), (5.3) and Theorem 5.1. Scalars
are nonnegative reals, so `1 - ε` is truncated at `0`. -/
def GrowthSetsConverge (growth : ℝ → Set Quadrant) (B : Set Quadrant) : Prop :=
  ∀ ε : ℝ≥0, 0 < ε → ∃ t₀ : ℝ≥0, ∀ t : ℝ≥0, t₀ ≤ t →
    (1 - ε) • B ⊆ t⁻¹ • growth (t : ℝ) ∧ t⁻¹ • growth (t : ℝ) ⊆ (1 + ε) • B

/-- Martin (2004), Theorem 5.1(i).

Under the tail conditions (5.1) and (5.2) and a positive mean weight, the shape function `g` exists and
is unique, and it has the following property. Almost surely, for every `ε > 0` and all large times `t`,
`(1 - ε) B ⊆ B(t) / t ⊆ (1 + ε) B`, where `B(t) = {x : T(⌊x⌋) ≤ t}` is the last-passage growth set and
`B = {x : g x ≤ 1}`. This is the case `d = 2`. -/
theorem lastPassage_growthSets_converge (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : HasSqrtLowerTail μ) (hpos : HasSqrtUpperTail μ) (hmean : 0 < weightMean μ) :
    (∃! g : Quadrant → ℝ, IsShapeFunction μ g) ∧
      ∀ g : Quadrant → ℝ, IsShapeFunction μ g →
        ∀ᵐ ω ∂environmentLaw μ,
          GrowthSetsConverge (lastPassageGrowthSet ω) (shapeSublevelSet g) := by
  sorry

/-- `h` grows at least linearly: `h x ≥ c ‖x‖` for some `c > 0`. For a homogeneous `h` this is
equivalent to the hypothesis `inf h(x)/‖x‖ > 0` of Martin (2004), Theorem 5.1(ii); the statement
uses this form. -/
def HasLinearLowerBound (h : Quadrant → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ x : Quadrant, c * taxicabNorm x ≤ h x

/-- Martin (2004), Theorem 5.1(ii).

Under the tail conditions (5.1) and (5.2), the first-passage shape function `h` exists and is unique, and
it has the following property. If `h x ≥ c ‖x‖` for some `c > 0` (for homogeneous `h`, the source's
condition `inf h(x)/‖x‖ > 0`), then almost surely, for every `ε > 0` and all large `t`,
`(1 - ε) C ⊆ C(t) / t ⊆ (1 + ε) C`, where `C(t) = {x : S(⌊x⌋) ≤ t}` and `C = {x : h x ≤ 1}`. This is
the case `d = 2`. -/
theorem firstPassage_growthSets_converge (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : HasSqrtLowerTail μ) (hpos : HasSqrtUpperTail μ) :
    (∃! h : Quadrant → ℝ, IsFirstPassageShapeFunction μ h) ∧
      ∀ h : Quadrant → ℝ, IsFirstPassageShapeFunction μ h →
        (HasLinearLowerBound h → ∀ᵐ ω ∂environmentLaw μ,
          GrowthSetsConverge (firstPassageGrowthSet ω) (shapeSublevelSet h)) := by
  sorry

/-! ### Section 5.1: Remark 5.1(i) -/

/-- Martin (2004), Remark 5.1(i), first sentence.

A homogeneous, symmetric, subadditive function `h` on the quadrant satisfies
`h x ≥ (‖x‖ / 2) h (1, 1)`. This is deterministic, and the case `d = 2`. -/
theorem taxicab_lower_bound_of_subadditive (h : Quadrant → ℝ) (hhom : IsHomogeneous h)
    (hsymm : IsSymmetric h) (hsub : IsSubadditive h) (x : Quadrant) :
    taxicabNorm x / 2 * h (1, 1) ≤ h x := by
  sorry

end LPPAudit.Martin2004
