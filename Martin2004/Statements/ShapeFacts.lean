/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Statements.ShapeDefinitions
public import LPP_Foundations.Shape.Uniqueness
public import Martin2004.Shape.FirstPassageShape
public import LPP_Foundations.Probability.Nondegenerate

/-!
# Uniqueness of shape functions

Facts used to show that the paper form of the shape statements ("there is exactly one shape
function, and it has the property `P`") agrees with the literal propositions `literal_<name>` in
the Martin statement modules ("there is exactly one function that is a shape function and has `P`"):

* `existsUnique_and_iff_of_unique`: if at most one `x` satisfies `p`, then
  `(∃! x, p x ∧ q x) ↔ (∃! x, p x) ∧ ∀ x, p x → q x`;
* `isShapeFunction_unique`: two shape functions of the same weight law are equal. This needs no
  moment or tail condition: it is `shapeCandidates_eq` of the module
  `LPPDifferentiability.Shape.Uniqueness`;
* `isFirstPassageShapeFunction_unique`: the same for first-passage shape functions, under the tail
  conditions (2.7) and (2.6) of Martin (2004), from `exists_unique_firstPassage_shape_martin`;
* `isExpectedRateLimitFunction_unique` and `isFirstPassageExpectedRateLimit_unique`: a function that
  is the limit of the expected rates in every direction is determined by those limits;
* `notAPointMass_iff_not_ae_const`: for a probability law, `NotAPointMass` holds exactly when the
  law is not almost surely constant;
* four theorems `..._form_iff` stating, clause by clause, that the paper form agrees with the
  literal form.

## References

* J. B. Martin, Limiting shape for directed percolation models, Ann. Probab. 32 (2004), Propositions
  2.1 and 2.2, Theorem 2.3, Corollary 2.5 and conditions (2.6) and (2.7).
-/

@[expose] public section

open LPPDifferentiability MeasureTheory Filter Set Asymptotics
open scoped NNReal ENNReal Topology Pointwise

namespace LPPStatements

/-- If at most one `x` satisfies `p`, then "exactly one `x` satisfies `p` and `q`" is the same as
"exactly one `x` satisfies `p`, and every `x` satisfying `p` satisfies `q`". -/
theorem existsUnique_and_iff_of_unique {α : Type*} {p q : α → Prop}
    (huniq : ∀ x y, p x → p y → x = y) :
    (∃! x, p x ∧ q x) ↔ (∃! x, p x) ∧ ∀ x, p x → q x := by
  constructor
  · rintro ⟨x, ⟨hp, hq⟩, -⟩
    refine ⟨⟨x, hp, fun y hy => huniq y x hy hp⟩, fun y hy => ?_⟩
    rw [huniq y x hy hp]
    exact hq
  · rintro ⟨⟨x, hp, -⟩, hq⟩
    exact ⟨x, ⟨hp, hq x hp⟩, fun y hy => huniq y x hy.1 hp⟩

/-- Two shape functions of the same weight law are equal: continuous homogeneous functions that both
approximate the last-passage time uniformly, almost surely, agree. No moment or tail condition is
needed. -/
theorem isShapeFunction_unique (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∀ g h : Quadrant → ℝ, IsShapeFunction μ g → IsShapeFunction μ h → g = h :=
  fun g h hg hh =>
    shapeCandidates_eq μ g h hg.1 hh.1 hg.2.1 hh.2.1 hg.2.2.2 hh.2.2.2

/-- Two first-passage shape functions of the same weight law are equal, under the tail conditions
(2.7) and (2.6) of Martin (2004). -/
theorem isFirstPassageShapeFunction_unique (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : HasSqrtLowerTail μ) (hpos : HasSqrtUpperTail μ) :
    ∀ g h : Quadrant → ℝ, IsFirstPassageShapeFunction μ g → IsFirstPassageShapeFunction μ h → g = h :=
  fun _ _ hg hh => (exists_unique_firstPassage_shape_martin μ hneg hpos).unique hg hh

/-- A function that is the limit of the expected last-passage rates in every direction is determined
by those limits. -/
theorem isExpectedRateLimitFunction_unique (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∀ g h : Quadrant → ℝ, IsExpectedRateLimitFunction μ g → IsExpectedRateLimitFunction μ h → g = h :=
  fun _ _ hg hh => funext fun x => tendsto_nhds_unique (hg.1 x) (hh.1 x)

/-- A function that is the limit of the expected first-passage rates in every direction is
determined by those limits. -/
theorem isFirstPassageExpectedRateLimit_unique (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∀ g h : Quadrant → ℝ, IsFirstPassageExpectedRateLimit μ g →
      IsFirstPassageExpectedRateLimit μ h → g = h :=
  fun _ _ hg hh => funext fun x => tendsto_nhds_unique (hg.1 x) (hh.1 x)

/-! ### The paper form against the literal form

Each statement below says: "there is exactly one shape function, and it has the property `P`" is the
same as "there is exactly one function that is a shape function and has `P`", the latter written out
clause by clause as in the literal statements. -/

/-- The paper form of a statement about the shape function of last-passage percolation, against the
literal form, written out. -/
theorem shapeFunction_form_iff (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (P : (Quadrant → ℝ) → Prop) :
    ((∃! g : Quadrant → ℝ, IsShapeFunction μ g) ∧ ∀ g : Quadrant → ℝ, IsShapeFunction μ g → P g) ↔
      ∃! g : Quadrant → ℝ,
        Continuous g ∧
        (∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x) ∧
        (∀ (x y : Quadrant) (a b : ℝ≥0), a + b = 1 →
          (a : ℝ) * g x + (b : ℝ) * g y ≤ g (a * x.1 + b * y.1, a * x.2 + b * y.2)) ∧
        (∀ᵐ ω ∂environmentLaw μ,
          ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ z : ℕ × ℕ, N ≤ z.1 + z.2 →
            |lastPassage ω (0, 0) z - g ((z.1 : ℝ≥0), (z.2 : ℝ≥0))| ≤ ε * ((z.1 + z.2 : ℕ) : ℝ)) ∧
        P g := by
  refine (existsUnique_and_iff_of_unique (isShapeFunction_unique μ)).symm.trans ?_
  simp only [IsShapeFunction, IsHomogeneous, IsConcaveOnQuadrant, ApproximatesLastPassage, and_assoc]

/-- The paper form of a statement about the shape function of first-passage percolation, against the
literal form, written out, under the tail conditions (2.7) and (2.6). -/
theorem firstPassageShapeFunction_form_iff (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : HasSqrtLowerTail μ) (hpos : HasSqrtUpperTail μ) (P : (Quadrant → ℝ) → Prop) :
    ((∃! h : Quadrant → ℝ, IsFirstPassageShapeFunction μ h) ∧
        ∀ h : Quadrant → ℝ, IsFirstPassageShapeFunction μ h → P h) ↔
      ∃! h : Quadrant → ℝ,
        Continuous h ∧
        (∀ (c : ℝ≥0) (x : Quadrant), h (c * x.1, c * x.2) = (c : ℝ) * h x) ∧
        (∀ (x y : Quadrant) (a b : ℝ≥0), a + b = 1 →
          h (a * x.1 + b * y.1, a * x.2 + b * y.2) ≤ (a : ℝ) * h x + (b : ℝ) * h y) ∧
        (∀ᵐ ω ∂environmentLaw μ,
          ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ z : ℕ × ℕ, N ≤ z.1 + z.2 →
            |firstPassage ω (0, 0) z - h ((z.1 : ℝ≥0), (z.2 : ℝ≥0))| ≤ ε * ((z.1 + z.2 : ℕ) : ℝ)) ∧
        P h := by
  refine (existsUnique_and_iff_of_unique (isFirstPassageShapeFunction_unique μ hneg hpos)).symm.trans ?_
  simp only [IsFirstPassageShapeFunction, IsHomogeneous, IsConvexOnQuadrant, ApproximatesFirstPassage,
    and_assoc]

/-- The paper form of Propositions 2.1-2.2 and Theorem 2.3 (the limit function is unique, and it is
continuous), against the literal form, written out. -/
theorem expectedRateLimit_continuous_form_iff (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ((∃! g : Quadrant → ℝ, IsExpectedRateLimitFunction μ g) ∧
        ∀ g : Quadrant → ℝ, IsExpectedRateLimitFunction μ g → Continuous g) ↔
      ∃! g : Quadrant → ℝ,
        (∀ x : Quadrant, Tendsto (fun n : ℕ =>
          (∫ ω : Environment, lastPassage ω 0
            (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
            ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (g x))) ∧
        (∀ a : ℕ × ℕ, ∀ᵐ ω ∂environmentLaw μ, Tendsto
          (fun n : ℕ => lastPassage ω 0 (n • a) / (n : ℝ)) atTop
          (𝓝 (g ((a.1 : ℝ≥0), (a.2 : ℝ≥0))))) ∧
        (∀ a : ℕ × ℕ, Tendsto (fun n : ℕ => ∫ ω : Environment,
          |lastPassage ω 0 (n • a) / (n : ℝ) - g ((a.1 : ℝ≥0), (a.2 : ℝ≥0))|
            ∂environmentLaw μ) atTop (𝓝 0)) ∧
        (∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x) ∧
        (∀ x : Quadrant, g (x.2, x.1) = g x) ∧
        (∀ x y : Quadrant, g x + g y ≤ g (x.1 + y.1, x.2 + y.2)) ∧
        Continuous g := by
  refine (existsUnique_and_iff_of_unique (isExpectedRateLimitFunction_unique μ)).symm.trans ?_
  simp only [IsExpectedRateLimitFunction, IsExpectedRateShape, HasAlmostSureLatticeRate,
    HasL1LatticeRate, IsHomogeneous, IsSymmetric, IsSuperadditive, and_assoc]

/-- The paper form of Corollary 2.5(i) (the first-passage limit function is unique, and it is
continuous), against the literal form, written out. -/
theorem firstPassageExpectedRateLimit_continuous_form_iff (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ((∃! h : Quadrant → ℝ, IsFirstPassageExpectedRateLimit μ h) ∧
        ∀ h : Quadrant → ℝ, IsFirstPassageExpectedRateLimit μ h → Continuous h) ↔
      ∃! h : Quadrant → ℝ,
        (∀ x : Quadrant, Tendsto (fun n : ℕ =>
          (∫ ω : Environment, firstPassage ω 0
            (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
            ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (h x))) ∧
        (∀ (c : ℝ≥0) (x : Quadrant), h (c * x.1, c * x.2) = (c : ℝ) * h x) ∧
        (∀ x : Quadrant, h (x.2, x.1) = h x) ∧
        (∀ x y : Quadrant, h (x.1 + y.1, x.2 + y.2) ≤ h x + h y) ∧
        Continuous h := by
  refine (existsUnique_and_iff_of_unique (isFirstPassageExpectedRateLimit_unique μ)).symm.trans ?_
  simp only [IsFirstPassageExpectedRateLimit, IsFirstPassageExpectedRateShape, IsHomogeneous,
    IsSymmetric, IsSubadditive, and_assoc]

/-! ### Nondegeneracy of the weight law -/

/-- For a probability law, `NotAPointMass μ` holds exactly when `μ` is not almost surely constant:
there is no value `c` such that `μ`-almost every `x` equals `c`. This uses no moment condition. -/
theorem notAPointMass_iff_not_ae_const (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    NotAPointMass μ ↔ ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, x = c :=
  forall_measure_singleton_lt_one_iff_not_exists_ae_eq μ

end LPPStatements
