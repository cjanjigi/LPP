/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Statements


/-!
# Solution: the limit shape of directed percolation (Martin 2004)

The definitions and statements are repeated from the Mathlib-only challenge. The path equivalence
preserves weights; finite extrema identify its supremum and infimum with the library passage times.
The main results then follow from the corresponding statements of Martin (2004) in the library.
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

/-- The first-passage time of the challenge, an infimum over paths, is the library's first-passage
time, the minimum of the weights of the finitely many paths. -/
theorem firstPassage_eq (ω : Environment) (u : Lattice) (d : ℕ × ℕ) :
    firstPassage ω u d = LPPDifferentiability.firstPassage ω u d := by
  classical
  obtain ⟨e, he⟩ := Path_equiv u d
  have hinf : firstPassage ω u d =
      ⨅ q : LPPDifferentiability.Path u d, LPPDifferentiability.pathWeight ω q :=
    (iInf_congr fun p => he ω p).trans (e.iInf_comp (g := LPPDifferentiability.pathWeight ω))
  rw [hinf]
  unfold LPPDifferentiability.firstPassage
  apply le_antisymm
  · refine Finset.le_min' _ _ _ fun y hy => ?_
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hy
    exact ciInf_le (Set.finite_range _).bddBelow q
  · refine le_ciInf fun q => Finset.min'_le _ _ ?_
    exact Finset.mem_image.mpr ⟨q, Finset.mem_univ q, rfl⟩

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
  simpa only [environmentLaw, LPPDifferentiability.environmentLaw, HasFiniteMean,
    LPPStatements.HasFiniteMean, IsHomogeneousExtended, LPPStatements.IsHomogeneousExtended,
    IsSymmetric, LPPStatements.IsSymmetric, IsSuperadditive, LPPStatements.IsSuperadditive,
    IsExtendedExpectedRateShape, LPPStatements.IsExtendedExpectedRateShape,
    IsExtendedAlmostSureShape, LPPStatements.IsExtendedAlmostSureShape, IsExtendedL1Shape,
    LPPStatements.IsExtendedL1Shape, IsExtendedShape, LPPStatements.IsExtendedShape,
    lastPassage_eq] using
    LPPStatements.Martin2004.extendedShape_limits_of_finite_mean μ hμ

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
  simpa only [environmentLaw, LPPDifferentiability.environmentLaw, HasFiniteMean,
    LPPStatements.HasFiniteMean, HasSqrtUpperTail, LPPStatements.HasSqrtUpperTail, IsHomogeneous,
    LPPStatements.IsHomogeneous, IsSymmetric, LPPStatements.IsSymmetric, IsSuperadditive,
    LPPStatements.IsSuperadditive, IsExpectedRateShape, LPPStatements.IsExpectedRateShape,
    HasAlmostSureLatticeRate, LPPStatements.HasAlmostSureLatticeRate, HasL1LatticeRate,
    LPPStatements.HasL1LatticeRate, IsExpectedRateLimitFunction,
    LPPStatements.IsExpectedRateLimitFunction, lastPassage_eq] using
    LPPStatements.Martin2004.shape_continuous_of_finite_mean μ hμ hpos

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
  simpa only [environmentLaw, LPPDifferentiability.environmentLaw, HasSqrtUpperTail,
    LPPStatements.HasSqrtUpperTail, HasSqrtLowerTail, LPPStatements.HasSqrtLowerTail,
    IsHomogeneous, LPPStatements.IsHomogeneous, IsConcaveOnQuadrant,
    LPPStatements.IsConcaveOnQuadrant, ApproximatesLastPassage,
    LPPStatements.ApproximatesLastPassage, IsShapeFunction, LPPStatements.IsShapeFunction,
    lastPassage_eq] using
    LPPStatements.Martin2004.shape_function_exists_unique μ hneg hpos

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
  simpa only [environmentLaw, LPPDifferentiability.environmentLaw, HasFiniteSecondMoment,
    LPPStatements.HasFiniteSecondMoment, HasSqrtUpperTail, LPPStatements.HasSqrtUpperTail,
    HasSqrtLowerTail, LPPStatements.HasSqrtLowerTail, weightMean, LPPStatements.weightMean,
    weightVariance, LPPStatements.weightVariance, weightStdDev, LPPStatements.weightStdDev,
    IsHomogeneous, LPPStatements.IsHomogeneous, IsConcaveOnQuadrant,
    LPPStatements.IsConcaveOnQuadrant, ApproximatesLastPassage,
    LPPStatements.ApproximatesLastPassage, IsShapeFunction, LPPStatements.IsShapeFunction,
    HasBoundaryAsymptotics, LPPStatements.HasBoundaryAsymptotics, lastPassage_eq] using
    LPPStatements.Martin2004.shape_boundary_asymptotics μ hneg hpos

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
  simpa only [environmentLaw, LPPDifferentiability.environmentLaw, HasFiniteMean,
    LPPStatements.HasFiniteMean, HasSqrtLowerTail, LPPStatements.HasSqrtLowerTail, IsHomogeneous,
    LPPStatements.IsHomogeneous, IsSymmetric, LPPStatements.IsSymmetric, IsSubadditive,
    LPPStatements.IsSubadditive, IsFirstPassageExpectedRateShape,
    LPPStatements.IsFirstPassageExpectedRateShape, IsFirstPassageExpectedRateLimit,
    LPPStatements.IsFirstPassageExpectedRateLimit, firstPassage_eq] using
    LPPStatements.Martin2004.firstPassageShape_continuous μ hμ hneg

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
  simpa only [environmentLaw, LPPDifferentiability.environmentLaw, HasFiniteSecondMoment,
    LPPStatements.HasFiniteSecondMoment, HasSqrtUpperTail, LPPStatements.HasSqrtUpperTail,
    HasSqrtLowerTail, LPPStatements.HasSqrtLowerTail, weightMean, LPPStatements.weightMean,
    weightVariance, LPPStatements.weightVariance, weightStdDev, LPPStatements.weightStdDev,
    IsHomogeneous, LPPStatements.IsHomogeneous, IsConvexOnQuadrant,
    LPPStatements.IsConvexOnQuadrant, ApproximatesLastPassage,
    LPPStatements.ApproximatesLastPassage, ApproximatesFirstPassage,
    LPPStatements.ApproximatesFirstPassage, IsFirstPassageShapeFunction,
    LPPStatements.IsFirstPassageShapeFunction, HasFirstPassageBoundaryAsymptotics,
    LPPStatements.HasFirstPassageBoundaryAsymptotics, lastPassage_eq, firstPassage_eq] using
    LPPStatements.Martin2004.firstPassageShape_boundary_asymptotics μ hneg hpos

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
  simpa only [environmentLaw, LPPDifferentiability.environmentLaw, HasSqrtUpperTail,
    LPPStatements.HasSqrtUpperTail, HasSqrtLowerTail, LPPStatements.HasSqrtLowerTail, weightMean,
    LPPStatements.weightMean, IsHomogeneous, LPPStatements.IsHomogeneous, IsConcaveOnQuadrant,
    LPPStatements.IsConcaveOnQuadrant, ApproximatesLastPassage,
    LPPStatements.ApproximatesLastPassage, IsShapeFunction, LPPStatements.IsShapeFunction,
    lastPassageGrowthSet, LPPStatements.lastPassageGrowthSet, shapeSublevelSet,
    LPPStatements.shapeSublevelSet, GrowthSetsConverge, LPPStatements.GrowthSetsConverge,
    lastPassage_eq] using
    LPPStatements.Martin2004.lastPassage_growthSets_converge μ hneg hpos hmean

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
  simpa only [environmentLaw, LPPDifferentiability.environmentLaw, HasSqrtUpperTail,
    LPPStatements.HasSqrtUpperTail, HasSqrtLowerTail, LPPStatements.HasSqrtLowerTail,
    IsHomogeneous, LPPStatements.IsHomogeneous, IsConvexOnQuadrant,
    LPPStatements.IsConvexOnQuadrant, taxicabNorm, LPPStatements.taxicabNorm,
    ApproximatesLastPassage, LPPStatements.ApproximatesLastPassage, ApproximatesFirstPassage,
    LPPStatements.ApproximatesFirstPassage, IsFirstPassageShapeFunction,
    LPPStatements.IsFirstPassageShapeFunction, firstPassageGrowthSet,
    LPPStatements.firstPassageGrowthSet, shapeSublevelSet, LPPStatements.shapeSublevelSet,
    GrowthSetsConverge, LPPStatements.GrowthSetsConverge, HasLinearLowerBound,
    LPPStatements.HasLinearLowerBound, lastPassage_eq, firstPassage_eq] using
    LPPStatements.Martin2004.firstPassage_growthSets_converge μ hneg hpos

/-! ### Section 5.1: Remark 5.1(i) -/

/-- Martin (2004), Remark 5.1(i), first sentence.

A homogeneous, symmetric, subadditive function `h` on the quadrant satisfies
`h x ≥ (‖x‖ / 2) h (1, 1)`. This is deterministic, and the case `d = 2`. -/
theorem taxicab_lower_bound_of_subadditive (h : Quadrant → ℝ) (hhom : IsHomogeneous h)
    (hsymm : IsSymmetric h) (hsub : IsSubadditive h) (x : Quadrant) :
    taxicabNorm x / 2 * h (1, 1) ≤ h x := by
  simpa only [IsHomogeneous, LPPStatements.IsHomogeneous, IsSymmetric, LPPStatements.IsSymmetric,
    IsSubadditive, LPPStatements.IsSubadditive, taxicabNorm, LPPStatements.taxicabNorm] using
    LPPStatements.Martin2004.taxicab_lower_bound_of_subadditive h hhom hsymm hsub x

end LPPAudit.Martin2004
