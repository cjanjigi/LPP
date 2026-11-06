/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Statements.ShapeDefinitions
public import Martin2004.Statements.ShapeFacts
public import Martin2004.Frozen.Martin.BoundaryAsymptotics
public import Martin2004.Frozen.Martin.FirstPassage
public import Martin2004.Frozen.Martin.FirstPassageBoundaryAsymptotics

/-!
# Boundary and first-passage statements of Martin (2004)

The two statement versions, their equivalence and descriptive theorem names for Theorem 2.4
and Corollary 2.5(i)-(ii), covering boundary asymptotics and first passage.
-/

@[expose] public section

open LPPDifferentiability MeasureTheory Filter Set Asymptotics
open scoped NNReal ENNReal Topology Pointwise

namespace LPPStatements.Martin2004
/-! ### Theorem 2.4 -/

/-- Version A of Martin (2004), Theorem 2.4: the statement
`LPPDifferentiability.martin_boundary_asymptotics` of the `Frozen` folder, copied verbatim. -/
def literal_shape_boundary_asymptotics : Prop :=
  ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (_hneg : (∫⁻ t in Iio (0 : ℝ), (μ (Iic t)) ^ (1 / 2 : ℝ)) < ∞)
    (_hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞),
    Integrable (fun t : ℝ => t ^ 2) μ ∧
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
      (fun α : ℝ≥0 => g (1, α) - ((∫ t : ℝ, t ∂μ) +
          2 * Real.sqrt (∫ t : ℝ, (t - ∫ s : ℝ, s ∂μ) ^ 2 ∂μ) * Real.sqrt (α : ℝ)))
        =o[𝓝[>] (0 : ℝ≥0)] (fun α : ℝ≥0 => Real.sqrt (α : ℝ))

/-- The theorem of the `Frozen` folder proves version A. -/
theorem literal_shape_boundary_asymptotics_holds : literal_shape_boundary_asymptotics :=
  LPPDifferentiability.martin_boundary_asymptotics

/-- Version B of Theorem 2.4: under the tail conditions (2.7) and (2.6), the weight has a finite
second moment, there is exactly one shape function, and it satisfies the boundary expansion (2.8)
with the mean and the standard deviation of the weight. -/
def plain_shape_boundary_asymptotics : Prop :=
  ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
    HasSqrtLowerTail μ → HasSqrtUpperTail μ →
      HasFiniteSecondMoment μ ∧
        (∃! g : Quadrant → ℝ, IsShapeFunction μ g) ∧
          ∀ g : Quadrant → ℝ, IsShapeFunction μ g →
            HasBoundaryAsymptotics g (weightMean μ) (weightStdDev μ)

/-- Versions A and B state the same thing. Shape functions are unique on their own,
so the paper form and version A agree (`ShapeFacts`). -/
theorem plain_shape_boundary_asymptotics_iff_literal :
    plain_shape_boundary_asymptotics ↔ literal_shape_boundary_asymptotics := by
  constructor
  · intro h μ _ hneg hpos
    exact ⟨(h μ hneg hpos).1, (shapeFunction_form_iff μ _).mp (h μ hneg hpos).2⟩
  · intro h μ _ hneg hpos
    exact ⟨(h μ hneg hpos).1, (shapeFunction_form_iff μ _).mpr (h μ hneg hpos).2⟩

/-- Martin (2004), Theorem 2.4 (`d = 2`).

Under the tail conditions (2.7) and (2.6), the weight has a finite second moment, and the shape
function exists and is unique, and it satisfies `g (1, α) = m + 2 s √α + o(√α)` as `α ↓ 0`, where
`m` is the mean and `s` the standard deviation of the weight. -/
theorem shape_boundary_asymptotics (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : HasSqrtLowerTail μ) (hpos : HasSqrtUpperTail μ) :
    HasFiniteSecondMoment μ ∧
      (∃! g : Quadrant → ℝ, IsShapeFunction μ g) ∧
        ∀ g : Quadrant → ℝ, IsShapeFunction μ g →
          HasBoundaryAsymptotics g (weightMean μ) (weightStdDev μ) :=
  plain_shape_boundary_asymptotics_iff_literal.mpr
    literal_shape_boundary_asymptotics_holds μ hneg hpos

/-- The paper label of `shape_boundary_asymptotics`. -/
alias theorem_2_4 := shape_boundary_asymptotics

/-! ### Corollary 2.5(i) -/

/-- Version A of Martin (2004), Corollary 2.5(i): the statement
`LPPDifferentiability.martin_first_passage_continuous` of the `Frozen` folder, copied verbatim. -/
def literal_firstPassageShape_continuous : Prop :=
  ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (_hμ : Integrable (fun t : ℝ => t) μ)
    (_hneg : (∫⁻ t in Iio (0 : ℝ), (μ (Iic t)) ^ (1 / 2 : ℝ)) < ∞),
    ∃! h : Quadrant → ℝ,
      (∀ x : Quadrant, Tendsto (fun n : ℕ =>
        (∫ ω : Environment, firstPassage ω 0
          (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
          ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (h x))) ∧
      (∀ (c : ℝ≥0) (x : Quadrant), h (c * x.1, c * x.2) = (c : ℝ) * h x) ∧
      (∀ x : Quadrant, h (x.2, x.1) = h x) ∧
      (∀ x y : Quadrant, h (x.1 + y.1, x.2 + y.2) ≤ h x + h y) ∧
      Continuous h

/-- The theorem of the `Frozen` folder proves version A. -/
theorem literal_firstPassageShape_continuous_holds : literal_firstPassageShape_continuous :=
  LPPDifferentiability.martin_first_passage_continuous

/-- Version B of Corollary 2.5(i): with a finite mean and the lower tail condition (2.7), there is
exactly one first-passage limit shape function, and it is continuous. -/
def plain_firstPassageShape_continuous : Prop :=
  ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
    HasFiniteMean μ → HasSqrtLowerTail μ →
      (∃! h : Quadrant → ℝ, IsFirstPassageExpectedRateLimit μ h) ∧
        ∀ h : Quadrant → ℝ, IsFirstPassageExpectedRateLimit μ h → Continuous h

/-- Versions A and B state the same thing. A limit function is determined by its expected rates,
so the paper form and version A agree (`ShapeFacts`). -/
theorem plain_firstPassageShape_continuous_iff_literal :
    plain_firstPassageShape_continuous ↔ literal_firstPassageShape_continuous := by
  constructor
  · intro h μ _ hμ hneg
    exact (firstPassageExpectedRateLimit_continuous_form_iff μ).mp (h μ hμ hneg)
  · intro h μ _ hμ hneg
    exact (firstPassageExpectedRateLimit_continuous_form_iff μ).mpr (h μ hμ hneg)

/-- Martin (2004), Corollary 2.5(i) (`d = 2`).

If the weight has a finite mean and satisfies the lower tail condition (2.7), the first-passage
limit shape function exists and is unique, and it is continuous on the closed quadrant. Here a
first-passage limit shape function is a real function `h` on the closed quadrant such that
`E S(⌊n x⌋) / n → h x` in every direction, where `S` is the first-passage time, and `h` is
homogeneous, symmetric and subadditive. -/
theorem firstPassageShape_continuous (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : HasFiniteMean μ) (hneg : HasSqrtLowerTail μ) :
    (∃! h : Quadrant → ℝ, IsFirstPassageExpectedRateLimit μ h) ∧
      ∀ h : Quadrant → ℝ, IsFirstPassageExpectedRateLimit μ h → Continuous h :=
  plain_firstPassageShape_continuous_iff_literal.mpr
    literal_firstPassageShape_continuous_holds μ hμ hneg

/-- The paper label of `firstPassageShape_continuous`. -/
alias corollary_2_5_i := firstPassageShape_continuous

/-! ### Corollary 2.5(ii) -/

/-- Version A of Martin (2004), Corollary 2.5(ii): the statement
`LPPDifferentiability.martin_first_passage_boundary_asymptotics` of the `Frozen` folder, copied
verbatim. -/
def literal_firstPassageShape_boundary_asymptotics : Prop :=
  ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (_hneg : (∫⁻ t in Iio (0 : ℝ), (μ (Iic t)) ^ (1 / 2 : ℝ)) < ∞)
    (_hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞),
    Integrable (fun t : ℝ => t ^ 2) μ ∧
    ∃! h : Quadrant → ℝ,
      Continuous h ∧
      (∀ (c : ℝ≥0) (x : Quadrant),
        h (c * x.1, c * x.2) = (c : ℝ) * h x) ∧
      (∀ (x y : Quadrant) (a b : ℝ≥0), a + b = 1 →
        h (a * x.1 + b * y.1, a * x.2 + b * y.2) ≤
          (a : ℝ) * h x + (b : ℝ) * h y) ∧
      (∀ᵐ ω ∂environmentLaw μ,
        ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ z : ℕ × ℕ,
          N ≤ z.1 + z.2 →
          |firstPassage ω (0, 0) z - h ((z.1 : ℝ≥0), (z.2 : ℝ≥0))| ≤
            ε * ((z.1 + z.2 : ℕ) : ℝ)) ∧
      (fun α : ℝ≥0 => h (1, α) - ((∫ t : ℝ, t ∂μ) -
          2 * Real.sqrt (∫ t : ℝ, (t - ∫ s : ℝ, s ∂μ) ^ 2 ∂μ) * Real.sqrt (α : ℝ)))
        =o[𝓝[>] (0 : ℝ≥0)] (fun α : ℝ≥0 => Real.sqrt (α : ℝ))

/-- The theorem of the `Frozen` folder proves version A. -/
theorem literal_firstPassageShape_boundary_asymptotics_holds :
    literal_firstPassageShape_boundary_asymptotics :=
  LPPDifferentiability.martin_first_passage_boundary_asymptotics

/-- Version B of Corollary 2.5(ii): under the tail conditions (2.7) and (2.6), the weight has a
finite second moment, there is exactly one first-passage shape function, and it satisfies the
boundary expansion with the mean and the standard deviation of the weight. -/
def plain_firstPassageShape_boundary_asymptotics : Prop :=
  ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
    HasSqrtLowerTail μ → HasSqrtUpperTail μ →
      HasFiniteSecondMoment μ ∧
        (∃! h : Quadrant → ℝ, IsFirstPassageShapeFunction μ h) ∧
          ∀ h : Quadrant → ℝ, IsFirstPassageShapeFunction μ h →
            HasFirstPassageBoundaryAsymptotics h (weightMean μ) (weightStdDev μ)

/-- Versions A and B state the same thing. First-passage shape functions are unique on their own,
under (2.7) and (2.6), so the paper form and version A agree (`ShapeFacts`). -/
theorem plain_firstPassageShape_boundary_asymptotics_iff_literal :
    plain_firstPassageShape_boundary_asymptotics ↔
      literal_firstPassageShape_boundary_asymptotics := by
  constructor
  · intro h μ _ hneg hpos
    exact ⟨(h μ hneg hpos).1, (firstPassageShapeFunction_form_iff μ hneg hpos _).mp (h μ hneg hpos).2⟩
  · intro h μ _ hneg hpos
    exact ⟨(h μ hneg hpos).1, (firstPassageShapeFunction_form_iff μ hneg hpos _).mpr (h μ hneg hpos).2⟩

/-- Martin (2004), Corollary 2.5(ii) (`d = 2`).

Under the tail conditions (2.7) and (2.6), the weight has a finite second moment, and the
first-passage shape function exists and is unique, and it satisfies `h (1, α) = m - 2 s √α + o(√α)`
as `α ↓ 0`, where `m` is the mean and `s` the standard deviation of the weight. Here a first-passage
shape function is a continuous, homogeneous, convex function `h` on the closed quadrant that
approximates the first-passage time `S(z)` within `ε ‖z‖` for all long `z`, almost surely. -/
theorem firstPassageShape_boundary_asymptotics (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : HasSqrtLowerTail μ) (hpos : HasSqrtUpperTail μ) :
    HasFiniteSecondMoment μ ∧
      (∃! h : Quadrant → ℝ, IsFirstPassageShapeFunction μ h) ∧
        ∀ h : Quadrant → ℝ, IsFirstPassageShapeFunction μ h →
          HasFirstPassageBoundaryAsymptotics h (weightMean μ) (weightStdDev μ) :=
  plain_firstPassageShape_boundary_asymptotics_iff_literal.mpr
    literal_firstPassageShape_boundary_asymptotics_holds μ hneg hpos

/-- The paper label of `firstPassageShape_boundary_asymptotics`. -/
alias corollary_2_5_ii := firstPassageShape_boundary_asymptotics

end LPPStatements.Martin2004
