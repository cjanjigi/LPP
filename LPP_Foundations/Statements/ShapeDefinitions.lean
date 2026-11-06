/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.LastPassage
public import LPP_Foundations.Frozen.Model.FirstPassage
public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import LPP_Foundations.Frozen.Model.Quadrant
public import LPP_Foundations.Frozen.Analysis.QuadrantExtension
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Algebra.Group.Pointwise.Set.Scalar

/-!
# Named definitions for the statements of the main results

Short definitions that let the main statements read like the papers: moment conditions on the weight
law, properties of a function on the closed quadrant, the shape function of last-passage and
first-passage percolation, the growth sets, and differentiability on the open quadrant.

Each definition unfolds, by `rfl`, to the text in the corresponding `literal_<name>` propositions
in the Statements modules, so a statement written with these definitions is equivalent to the
literal one without any change of mathematics.

## References

* J. B. Martin, Limiting shape for directed percolation models, Ann. Probab. 32 (2004), Section 2,
  Section 5.1 and Theorem 5.1.
* C. Janjigian, F. Rassoul-Agha and T. Seppäläinen, *Differentiability of the shape function in the
  planar corner growth model*, preprint: assumptions (A1)-(A3), the shape theorem (2.3) and
  Theorem 2.1.
-/

@[expose] public section

open LPPDifferentiability MeasureTheory Filter Set Asymptotics
open scoped NNReal ENNReal Topology Pointwise

namespace LPPStatements

/-! ### Conditions on the weight law -/

/-- The weight law `μ` is not a point mass: no single value carries all of the probability.
This is assumption (A1) of the differentiability preprint. For a probability law this holds exactly
when `μ` is not almost surely constant (`LPPStatements.notAPointMass_iff_not_ae_const`). -/
def NotAPointMass (μ : Measure ℝ) : Prop :=
  ∀ c : ℝ, μ ({c} : Set ℝ) < 1

/-- The negative part of the weight has a finite moment of some order `q > p`.
For `p = 1` this is assumption (A2) of the differentiability preprint: `E[(w⁻)^q] < ∞` for some
`q > 1`. -/
def HasNegativePartMomentAbove (μ : Measure ℝ) (p : ℝ) : Prop :=
  ∃ q : ℝ, p < q ∧ (∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ q) ∂μ) < ∞

/-- The positive part of the weight has a finite moment of some order `q > p`.
For `p = 4` this is assumption (A3) of the differentiability preprint: `E[(w⁺)^q] < ∞` for some
`q > 4`. -/
def HasPositivePartMomentAbove (μ : Measure ℝ) (p : ℝ) : Prop :=
  ∃ q : ℝ, p < q ∧ (∫⁻ t, ENNReal.ofReal ((max t 0) ^ q) ∂μ) < ∞

/-- The weight has a finite mean, `E |X| < ∞`: Martin (2004), condition (2.4), the hypothesis of
Proposition 2.1. -/
def HasFiniteMean (μ : Measure ℝ) : Prop :=
  Integrable (fun t : ℝ => t) μ

/-- The weight has a finite second moment, so its variance `σ²` exists: the standing assumption of
Martin (2004), Theorem 2.4 and Corollary 2.5(ii). -/
def HasFiniteSecondMoment (μ : Measure ℝ) : Prop :=
  Integrable (fun t : ℝ => t ^ 2) μ

/-- The upper tail of the weight is integrable in the square-root sense:
`∫₀^∞ (1 - F(s))^(1/2) ds < ∞`, where `1 - F(s) = μ (s, ∞)`. This is Martin (2004), condition (2.6),
and the case `d = 2` of conditions (2.5) and (5.2). -/
def HasSqrtUpperTail (μ : Measure ℝ) : Prop :=
  (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞

/-- The lower tail of the weight is integrable in the square-root sense:
`∫_{-∞}^0 F(s)^(1/2) ds < ∞`, where `F(s) = μ (-∞, s]`. This is Martin (2004), condition (2.7), and
the case `d = 2` of condition (5.1). -/
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

/-! ### Properties of a function on the closed quadrant -/

/-- `g` is positively homogeneous: `g (c x) = c g x` for every scalar `c ≥ 0`.
Martin (2004), Proposition 2.1(ii). -/
def IsHomogeneous (g : Quadrant → ℝ) : Prop :=
  ∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x

/-- `g` with values in the extended reals is positively homogeneous: `g (c x) = c g x` for every
`c ≥ 0`. Martin (2004), Proposition 2.1(ii), in the generality where `g x = +∞` is allowed; the
product is Mathlib's product in `EReal`, with the convention `0 * ⊤ = 0`. -/
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
`a + b = 1`. This is the concavity of the shape function (differentiability preprint, Section 2). -/
def IsConcaveOnQuadrant (g : Quadrant → ℝ) : Prop :=
  ∀ (x y : Quadrant) (a b : ℝ≥0), a + b = 1 →
    (a : ℝ) * g x + (b : ℝ) * g y ≤ g (a * x.1 + b * y.1, a * x.2 + b * y.2)

/-- `h` is convex on the quadrant, in the form `h (a x + b y) ≤ a h x + b h y` for `a, b ≥ 0` with
`a + b = 1`. This is the convexity of the first-passage shape function (Martin (2004), Section 5.1,
"C is convex"). -/
def IsConvexOnQuadrant (h : Quadrant → ℝ) : Prop :=
  ∀ (x y : Quadrant) (a b : ℝ≥0), a + b = 1 →
    h (a * x.1 + b * y.1, a * x.2 + b * y.2) ≤ (a : ℝ) * h x + (b : ℝ) * h y

/-- The taxicab norm `‖x‖ = x₁ + x₂` of a point of the closed quadrant (the norm of
Martin (2004), Theorem 5.1(ii) and Remark 5.1(i) for `d = 2`; `|z|₁` in the differentiability
preprint). -/
def taxicabNorm (x : Quadrant) : ℝ :=
  (x.1 : ℝ) + x.2

/-! ### Shape functions of last-passage and first-passage percolation -/

/-- `g` approximates the last-passage time uniformly, almost surely: for almost every environment
`ω` and every `ε > 0`, `|T(0, z) - g z| ≤ ε ‖z‖` for all lattice points `z` far enough from the
origin. This is (2.3) of the differentiability preprint, and the content of
Martin (2004), Theorem 5.1 before taking growth sets. -/
def ApproximatesLastPassage (μ : Measure ℝ) [IsProbabilityMeasure μ] (g : Quadrant → ℝ) :
    Prop :=
  ∀ᵐ ω ∂environmentLaw μ,
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ z : ℕ × ℕ,
      N ≤ z.1 + z.2 →
      |lastPassage ω (0, 0) z - g ((z.1 : ℝ≥0), (z.2 : ℝ≥0))| ≤
        ε * ((z.1 + z.2 : ℕ) : ℝ)

/-- `h` approximates the first-passage time `S` uniformly, almost surely: for almost every
environment `ω` and every `ε > 0`, `|S(0, z) - h z| ≤ ε ‖z‖` for all lattice points `z` far enough
from the origin. The first-passage analogue of `ApproximatesLastPassage`; Martin (2004),
Section 5.1 and Corollary 2.5(ii). -/
def ApproximatesFirstPassage (μ : Measure ℝ) [IsProbabilityMeasure μ] (h : Quadrant → ℝ) :
    Prop :=
  ∀ᵐ ω ∂environmentLaw μ,
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ z : ℕ × ℕ,
      N ≤ z.1 + z.2 →
      |firstPassage ω (0, 0) z - h ((z.1 : ℝ≥0), (z.2 : ℝ≥0))| ≤
        ε * ((z.1 + z.2 : ℕ) : ℝ)

/-- `g` is a shape function of the weight law `μ` (last-passage percolation): continuous on the
closed quadrant, positively homogeneous, concave, and approximating the last-passage time
uniformly almost surely. This is the function `g` of Martin (2004), Section 2 and Theorem 5.1, and
of the differentiability preprint, Section 2. -/
def IsShapeFunction (μ : Measure ℝ) [IsProbabilityMeasure μ] (g : Quadrant → ℝ) : Prop :=
  Continuous g ∧ IsHomogeneous g ∧ IsConcaveOnQuadrant g ∧ ApproximatesLastPassage μ g

/-- `h` is a shape function of the weight law `μ` for first-passage percolation: continuous on the
closed quadrant, positively homogeneous, convex, and approximating the first-passage time
uniformly almost surely. This is the function `h` of Martin (2004), (2.10), Corollary 2.5 and
Theorem 5.1(ii). -/
def IsFirstPassageShapeFunction (μ : Measure ℝ) [IsProbabilityMeasure μ] (h : Quadrant → ℝ) :
    Prop :=
  Continuous h ∧ IsHomogeneous h ∧ IsConvexOnQuadrant h ∧ ApproximatesFirstPassage μ h

/-- A function `g` on the closed quadrant is differentiable at every point of the open quadrant
`x₁ > 0, x₂ > 0`. The function is extended to the plane by `quadrantExtension`, so the
differentiability is the ordinary one of a function on `ℝ × ℝ`. This is Theorem 2.1 of the
differentiability preprint. -/
def DifferentiableOnOpenQuadrant (g : Quadrant → ℝ) : Prop :=
  ∀ x : ℝ × ℝ, 0 < x.1 → 0 < x.2 → DifferentiableAt ℝ (quadrantExtension g) x

/-! ### The limit of expected passage times (Martin (2004), Section 2) -/

/-- `g` is the limit of the expected last-passage rates in every direction: for every `x` in the
closed quadrant, `E T(⌊n x⌋) / n → g x`. Martin (2004) writes `g` as the supremum (2.3) of these
rates; Proposition 2.1 uses the limit, which is what this definition states. -/
def IsExpectedRateShape (μ : Measure ℝ) [IsProbabilityMeasure μ] (g : Quadrant → ℝ) : Prop :=
  ∀ x : Quadrant, Tendsto (fun n : ℕ =>
    (∫ ω : Environment, lastPassage ω 0
      (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
      ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (g x))

/-- `h` is the limit of the expected first-passage rates in every direction: for every `x` in the
closed quadrant, `E S(⌊n x⌋) / n → h x`. Martin (2004) writes `h` as the infimum (2.10) of these
rates; the limit is what this definition states. -/
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

/-- `g`, with values in the extended reals, has all the properties of Martin (2004),
Proposition 2.1 (literal form, finite mean): the expected rate, the almost sure limit, the `L¹`
limit where finite, homogeneity, symmetry and superadditivity. -/
def IsExtendedShape (μ : Measure ℝ) [IsProbabilityMeasure μ] (g : Quadrant → EReal) : Prop :=
  IsExtendedExpectedRateShape μ g ∧ IsExtendedAlmostSureShape μ g ∧ IsExtendedL1Shape μ g ∧
    IsHomogeneousExtended g ∧ IsSymmetric g ∧ IsSuperadditive g

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
def IsExpectedRateLimitFunction (μ : Measure ℝ) [IsProbabilityMeasure μ] (g : Quadrant → ℝ) : Prop :=
  IsExpectedRateShape μ g ∧ HasAlmostSureLatticeRate μ g ∧ HasL1LatticeRate μ g ∧
    IsHomogeneous g ∧ IsSymmetric g ∧ IsSuperadditive g

/-- `h` is a first-passage limit shape function in the sense of Martin (2004), (2.10) and
Corollary 2.5(i): the limit of the expected first-passage rate in every direction, homogeneous,
symmetric and subadditive. Continuity is not included; it is the content of Corollary 2.5(i). -/
def IsFirstPassageExpectedRateLimit (μ : Measure ℝ) [IsProbabilityMeasure μ] (h : Quadrant → ℝ) :
    Prop :=
  IsFirstPassageExpectedRateShape μ h ∧ IsHomogeneous h ∧ IsSymmetric h ∧ IsSubadditive h

/-! ### Behavior near the boundary of the quadrant -/

/-- Martin (2004), (2.8): `g (1, α) = m + 2 s √α + o(√α)` as `α ↓ 0`, where `m` is the mean and
`s` the standard deviation of the weight. -/
def HasBoundaryAsymptotics (g : Quadrant → ℝ) (m s : ℝ) : Prop :=
  (fun α : ℝ≥0 => g (1, α) - (m + 2 * s * Real.sqrt (α : ℝ)))
    =o[𝓝[>] (0 : ℝ≥0)] (fun α : ℝ≥0 => Real.sqrt (α : ℝ))

/-- Martin (2004), Corollary 2.5(ii): `h (1, α) = m - 2 s √α + o(√α)` as `α ↓ 0`, where `m` is the
mean and `s` the standard deviation of the weight. -/
def HasFirstPassageBoundaryAsymptotics (h : Quadrant → ℝ) (m s : ℝ) : Prop :=
  (fun α : ℝ≥0 => h (1, α) - (m - 2 * s * Real.sqrt (α : ℝ)))
    =o[𝓝[>] (0 : ℝ≥0)] (fun α : ℝ≥0 => Real.sqrt (α : ℝ))

/-! ### Growth sets (Martin (2004), Section 5.1) -/

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

/-- `h` grows at least linearly: `h x ≥ c ‖x‖` for some `c > 0`. For a homogeneous `h` this is
equivalent to the hypothesis `inf h(x)/‖x‖ > 0` of Martin (2004), Theorem 5.1(ii); the statement
uses this form. -/
def HasLinearLowerBound (h : Quadrant → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ x : Quadrant, c * taxicabNorm x ≤ h x

end LPPStatements
