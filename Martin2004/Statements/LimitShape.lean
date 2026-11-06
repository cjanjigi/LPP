/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Statements.ShapeDefinitions
public import Martin2004.Statements.ShapeFacts
public import Martin2004.Frozen.Martin.Proposition21
public import Martin2004.Frozen.Martin.ShapeContinuous
public import Martin2004.Frozen.Martin.Shape

/-!
# Limit shape statements of Martin (2004)

The two statement versions, their equivalence and descriptive theorem names for Proposition 2.1,
Propositions 2.1-2.2 with Theorem 2.3, and the uniform shape statement of Section 5.3.
-/

@[expose] public section

open LPPDifferentiability MeasureTheory Filter Set Asymptotics
open scoped NNReal ENNReal Topology Pointwise

namespace LPPStatements.Martin2004

/-! ### Proposition 2.1 -/

/-- Version A of Martin (2004), Proposition 2.1: the statement
`LPPDifferentiability.martin_prop_2_1` of the `Frozen` folder, copied verbatim. -/
def literal_extendedShape_limits_of_finite_mean : Prop :=
  ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (_hμ : Integrable (fun t : ℝ => t) μ),
    ∃! g : Quadrant → EReal,
      (∀ x : Quadrant, Tendsto (fun n : ℕ =>
        (((∫ ω : Environment, lastPassage ω 0
          (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
          ∂environmentLaw μ) / (n : ℝ) : ℝ) : EReal)) atTop (𝓝 (g x))) ∧
      (∀ x : Quadrant, ∀ᵐ ω ∂environmentLaw μ, Tendsto (fun n : ℕ =>
        ((lastPassage ω 0 (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) /
          (n : ℝ) : ℝ) : EReal)) atTop (𝓝 (g x))) ∧
      (∀ x : Quadrant, g x ≠ ⊤ → Tendsto (fun n : ℕ => ∫ ω : Environment,
        |lastPassage ω 0 (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) /
          (n : ℝ) - (g x).toReal| ∂environmentLaw μ) atTop (𝓝 0)) ∧
      (∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = ((c : ℝ) : EReal) * g x) ∧
      (∀ x : Quadrant, g (x.2, x.1) = g x) ∧
      (∀ x y : Quadrant, g x + g y ≤ g (x.1 + y.1, x.2 + y.2))

/-- The theorem of the `Frozen` folder proves version A. -/
theorem literal_extendedShape_limits_of_finite_mean_holds :
    literal_extendedShape_limits_of_finite_mean :=
  LPPDifferentiability.martin_prop_2_1

/-- Version B of Proposition 2.1: if the weight has a finite mean, there is exactly one
extended-real function on the closed quadrant with all the properties of `IsExtendedShape`. -/
def plain_extendedShape_limits_of_finite_mean : Prop :=
  ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
    HasFiniteMean μ → ∃! g : Quadrant → EReal, IsExtendedShape μ g

/-- Versions A and B are definitionally the same statement. -/
theorem plain_extendedShape_limits_of_finite_mean_iff_literal :
    plain_extendedShape_limits_of_finite_mean ↔ literal_extendedShape_limits_of_finite_mean :=
  Iff.rfl

/-- Martin (2004), Proposition 2.1 (literal form, `d = 2`).

If the weight has a finite mean, there is exactly one function `g` from the closed quadrant to the
extended reals such that: in every real direction `x`, the normalized expected last-passage time
`E T(⌊n x⌋) / n` and, almost surely, `T(⌊n x⌋) / n` converge to `g x`; the convergence also holds in
`L¹` wherever `g x` is finite; `g` is positively homogeneous, symmetric and superadditive. The value
`+∞` is allowed. -/
theorem extendedShape_limits_of_finite_mean (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : HasFiniteMean μ) : ∃! g : Quadrant → EReal, IsExtendedShape μ g :=
  plain_extendedShape_limits_of_finite_mean_iff_literal.mpr
    literal_extendedShape_limits_of_finite_mean_holds μ hμ

/-- The paper label of `extendedShape_limits_of_finite_mean`. -/
alias proposition_2_1 := extendedShape_limits_of_finite_mean

/-! ### Propositions 2.1-2.2 and Theorem 2.3, finite form -/

/-- Version A of Martin (2004), Propositions 2.1-2.2 and Theorem 2.3: the statement
`LPPDifferentiability.martin_shape_continuous` of the `Frozen` folder, copied verbatim. -/
def literal_shape_continuous_of_finite_mean : Prop :=
  ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (_hμ : Integrable (fun t : ℝ => t) μ)
    (_hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞),
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
      Continuous g

/-- The theorem of the `Frozen` folder proves version A. -/
theorem literal_shape_continuous_of_finite_mean_holds :
    literal_shape_continuous_of_finite_mean :=
  LPPDifferentiability.martin_shape_continuous

/-- Version B of Propositions 2.1-2.2 and Theorem 2.3: with a finite mean and the upper tail
condition (2.6), there is exactly one real-valued limit shape function, and it is continuous. -/
def plain_shape_continuous_of_finite_mean : Prop :=
  ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
    HasFiniteMean μ → HasSqrtUpperTail μ →
      (∃! g : Quadrant → ℝ, IsExpectedRateLimitFunction μ g) ∧
        ∀ g : Quadrant → ℝ, IsExpectedRateLimitFunction μ g → Continuous g

/-- Versions A and B state the same thing. A limit function is determined by its expected rates,
so the paper form and version A agree (`ShapeFacts`). -/
theorem plain_shape_continuous_of_finite_mean_iff_literal :
    plain_shape_continuous_of_finite_mean ↔ literal_shape_continuous_of_finite_mean := by
  constructor
  · intro h μ _ hμ hpos
    exact (expectedRateLimit_continuous_form_iff μ).mp (h μ hμ hpos)
  · intro h μ _ hμ hpos
    exact (expectedRateLimit_continuous_form_iff μ).mpr (h μ hμ hpos)

/-- Martin (2004), Propositions 2.1-2.2 and Theorem 2.3 (finite form, `d = 2`).

If the weight has a finite mean and satisfies the upper tail condition (2.6), the limit shape
function exists and is unique, and it is continuous. Here a limit shape function is a real function
`g` on the closed quadrant such that `E T(⌊n x⌋) / n → g x` in every real direction; along every
lattice direction `T(n a) / n → g a` almost surely and in `L¹`; and `g` is homogeneous, symmetric
and superadditive. The continuity holds on the whole closed quadrant, boundary included. -/
theorem shape_continuous_of_finite_mean (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : HasFiniteMean μ) (hpos : HasSqrtUpperTail μ) :
    (∃! g : Quadrant → ℝ, IsExpectedRateLimitFunction μ g) ∧
      ∀ g : Quadrant → ℝ, IsExpectedRateLimitFunction μ g → Continuous g :=
  plain_shape_continuous_of_finite_mean_iff_literal.mpr
    literal_shape_continuous_of_finite_mean_holds μ hμ hpos

/-- The paper label of `shape_continuous_of_finite_mean`. -/
alias propositions_2_1_2_2_theorem_2_3 := shape_continuous_of_finite_mean

/-! ### Section 5.3, the uniform shape statement -/

/-- Version A of Martin (2004), Section 5.3 (the uniform shape statement): the statement
`LPPDifferentiability.exists_unique_shape_martin` of the `Frozen` folder, copied verbatim. -/
def literal_shape_function_exists_unique : Prop :=
  ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (_hneg : (∫⁻ t in Iio (0 : ℝ), (μ (Iic t)) ^ (1 / 2 : ℝ)) < ∞)
    (_hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞),
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
            ε * ((z.1 + z.2 : ℕ) : ℝ))

/-- The theorem of the `Frozen` folder proves version A. -/
theorem literal_shape_function_exists_unique_holds : literal_shape_function_exists_unique :=
  LPPDifferentiability.exists_unique_shape_martin

/-- Version B of the uniform shape statement (Section 5.3): under the lower tail condition (2.7) and
the upper tail condition (2.6), there is exactly one function that is a shape function. -/
def plain_shape_function_exists_unique : Prop :=
  ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
    HasSqrtLowerTail μ → HasSqrtUpperTail μ → ∃! g : Quadrant → ℝ, IsShapeFunction μ g

/-- Versions A and B state the same thing. -/
theorem plain_shape_function_exists_unique_iff_literal :
    plain_shape_function_exists_unique ↔ literal_shape_function_exists_unique :=
  Iff.rfl

/-- Martin (2004), Section 5.3 (the uniform shape statement behind Theorem 5.1), with Proposition
2.1 and Theorem 2.3, `d = 2`.

If the weight satisfies the tail conditions (2.7) and (2.6), there is exactly one continuous,
homogeneous, concave function `g` on the closed quadrant that approximates the last-passage time
`T(z)` within `ε ‖z‖` for all long `z`, almost surely. -/
theorem shape_function_exists_unique (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : HasSqrtLowerTail μ) (hpos : HasSqrtUpperTail μ) :
    ∃! g : Quadrant → ℝ, IsShapeFunction μ g :=
  plain_shape_function_exists_unique_iff_literal.mpr
    literal_shape_function_exists_unique_holds μ hneg hpos

/-- The paper label of `shape_function_exists_unique`. -/
alias section_5_3_uniform_shape := shape_function_exists_unique

end LPPStatements.Martin2004
