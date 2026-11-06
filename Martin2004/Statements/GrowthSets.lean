/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Statements.ShapeDefinitions
public import Martin2004.Statements.ShapeFacts
public import Martin2004.Frozen.Martin.GrowthShape
public import Martin2004.Frozen.Martin.FirstPassageGrowthShape
public import Martin2004.Frozen.Martin.Remark51

/-!
# Growth-set statements of Martin (2004)

The two statement versions, their equivalence and descriptive theorem names for Theorem 5.1(i)-(ii)
and Remark 5.1(i), covering growth sets and the deterministic lower bound.
-/

@[expose] public section

open LPPDifferentiability MeasureTheory Filter Set Asymptotics
open scoped NNReal ENNReal Topology Pointwise

namespace LPPStatements.Martin2004
/-! ### Theorem 5.1(i) -/

/-- Version A of Martin (2004), Theorem 5.1(i): the statement
`LPPDifferentiability.martin_last_passage_growth_shape` of the `Frozen` folder, copied verbatim. -/
def literal_lastPassage_growthSets_converge : Prop :=
  ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (_hneg : (∫⁻ t in Iio (0 : ℝ), (μ (Iic t)) ^ (1 / 2 : ℝ)) < ∞)
    (_hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞)
    (_hmean : 0 < ∫ t : ℝ, t ∂μ),
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
      (∀ᵐ ω ∂environmentLaw μ, ∀ ε : ℝ≥0, 0 < ε → ∃ t₀ : ℝ≥0, ∀ t : ℝ≥0, t₀ ≤ t →
        (1 - ε) • {x : Quadrant | g x ≤ 1} ⊆
            t⁻¹ • {x : Quadrant | lastPassage ω 0 (⌊x.1⌋₊, ⌊x.2⌋₊) ≤ (t : ℝ)} ∧
          t⁻¹ • {x : Quadrant | lastPassage ω 0 (⌊x.1⌋₊, ⌊x.2⌋₊) ≤ (t : ℝ)} ⊆
            (1 + ε) • {x : Quadrant | g x ≤ 1})

/-- The theorem of the `Frozen` folder proves version A. -/
theorem literal_lastPassage_growthSets_converge_holds :
    literal_lastPassage_growthSets_converge :=
  LPPDifferentiability.martin_last_passage_growth_shape

/-- Version B of Theorem 5.1(i): under the tail conditions (5.1) and (5.2) and a positive mean,
there is exactly one shape function `g`, and almost surely the last-passage growth sets `B(t)`,
rescaled by `1/t`, converge to `B = {x : g x ≤ 1}`. -/
def plain_lastPassage_growthSets_converge : Prop :=
  ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
    HasSqrtLowerTail μ → HasSqrtUpperTail μ → 0 < weightMean μ →
      (∃! g : Quadrant → ℝ, IsShapeFunction μ g) ∧
        ∀ g : Quadrant → ℝ, IsShapeFunction μ g →
          ∀ᵐ ω ∂environmentLaw μ,
            GrowthSetsConverge (lastPassageGrowthSet ω) (shapeSublevelSet g)

/-- Versions A and B state the same thing. Shape functions are unique on their own,
so the paper form and version A agree (`ShapeFacts`). -/
theorem plain_lastPassage_growthSets_converge_iff_literal :
    plain_lastPassage_growthSets_converge ↔ literal_lastPassage_growthSets_converge := by
  constructor
  · intro h μ _ hneg hpos hmean
    exact (shapeFunction_form_iff μ _).mp (h μ hneg hpos hmean)
  · intro h μ _ hneg hpos hmean
    exact (shapeFunction_form_iff μ _).mpr (h μ hneg hpos hmean)

/-- Martin (2004), Theorem 5.1(i) (growth-set form, `d = 2`).

Under the tail conditions (5.1) and (5.2) and a positive mean weight, the shape function `g` exists
and is unique, and it has the following property. Almost surely, for every `ε > 0` and all large
times `t`, `(1 - ε) B ⊆ B(t) / t ⊆ (1 + ε) B`, where `B(t) = {x : T(⌊x⌋) ≤ t}` is the last-passage
growth set and `B = {x : g x ≤ 1}`. -/
theorem lastPassage_growthSets_converge (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : HasSqrtLowerTail μ) (hpos : HasSqrtUpperTail μ) (hmean : 0 < weightMean μ) :
    (∃! g : Quadrant → ℝ, IsShapeFunction μ g) ∧
      ∀ g : Quadrant → ℝ, IsShapeFunction μ g →
        ∀ᵐ ω ∂environmentLaw μ,
          GrowthSetsConverge (lastPassageGrowthSet ω) (shapeSublevelSet g) :=
  plain_lastPassage_growthSets_converge_iff_literal.mpr
    literal_lastPassage_growthSets_converge_holds μ hneg hpos hmean

/-- The paper label of `lastPassage_growthSets_converge`. -/
alias theorem_5_1_i := lastPassage_growthSets_converge

/-! ### Theorem 5.1(ii) -/

/-- Version A of Martin (2004), Theorem 5.1(ii): the statement
`LPPDifferentiability.martin_first_passage_growth_shape` of the `Frozen` folder, copied verbatim. -/
def literal_firstPassage_growthSets_converge : Prop :=
  ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (_hneg : (∫⁻ t in Iio (0 : ℝ), (μ (Iic t)) ^ (1 / 2 : ℝ)) < ∞)
    (_hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞),
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
      ((∃ c : ℝ, 0 < c ∧ ∀ x : Quadrant, c * ((x.1 : ℝ) + x.2) ≤ h x) →
        ∀ᵐ ω ∂environmentLaw μ, ∀ ε : ℝ≥0, 0 < ε → ∃ t₀ : ℝ≥0, ∀ t : ℝ≥0, t₀ ≤ t →
          (1 - ε) • {x : Quadrant | h x ≤ 1} ⊆
              t⁻¹ • {x : Quadrant | firstPassage ω 0 (⌊x.1⌋₊, ⌊x.2⌋₊) ≤ (t : ℝ)} ∧
            t⁻¹ • {x : Quadrant | firstPassage ω 0 (⌊x.1⌋₊, ⌊x.2⌋₊) ≤ (t : ℝ)} ⊆
              (1 + ε) • {x : Quadrant | h x ≤ 1})

/-- The theorem of the `Frozen` folder proves version A. -/
theorem literal_firstPassage_growthSets_converge_holds :
    literal_firstPassage_growthSets_converge :=
  LPPDifferentiability.martin_first_passage_growth_shape

/-- Version B of Theorem 5.1(ii): under the tail conditions (5.1) and (5.2), there is exactly one
first-passage shape function `h`, and if `h x ≥ c ‖x‖` for some `c > 0` then almost surely the
first-passage growth sets `C(t)`, rescaled by `1/t`, converge to `C = {x : h x ≤ 1}`. -/
def plain_firstPassage_growthSets_converge : Prop :=
  ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
    HasSqrtLowerTail μ → HasSqrtUpperTail μ →
      (∃! h : Quadrant → ℝ, IsFirstPassageShapeFunction μ h) ∧
        ∀ h : Quadrant → ℝ, IsFirstPassageShapeFunction μ h →
          (HasLinearLowerBound h → ∀ᵐ ω ∂environmentLaw μ,
            GrowthSetsConverge (firstPassageGrowthSet ω) (shapeSublevelSet h))

/-- Versions A and B state the same thing. First-passage shape functions are unique on their own,
under (5.1) and (5.2), so the paper form and version A agree (`ShapeFacts`). -/
theorem plain_firstPassage_growthSets_converge_iff_literal :
    plain_firstPassage_growthSets_converge ↔ literal_firstPassage_growthSets_converge := by
  constructor
  · intro h μ _ hneg hpos
    exact (firstPassageShapeFunction_form_iff μ hneg hpos _).mp (h μ hneg hpos)
  · intro h μ _ hneg hpos
    exact (firstPassageShapeFunction_form_iff μ hneg hpos _).mpr (h μ hneg hpos)

/-- Martin (2004), Theorem 5.1(ii) (growth-set form, `d = 2`).

Under the tail conditions (5.1) and (5.2), the first-passage shape function `h` exists and is
unique, and it has the following property. If `h x ≥ c ‖x‖` for some `c > 0` (for homogeneous `h`,
Martin's condition `inf h(x)/‖x‖ > 0`), then almost surely, for every `ε > 0` and all large `t`,
`(1 - ε) C ⊆ C(t) / t ⊆ (1 + ε) C`, where `C(t) = {x : S(⌊x⌋) ≤ t}` and `C = {x : h x ≤ 1}`. -/
theorem firstPassage_growthSets_converge (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : HasSqrtLowerTail μ) (hpos : HasSqrtUpperTail μ) :
    (∃! h : Quadrant → ℝ, IsFirstPassageShapeFunction μ h) ∧
      ∀ h : Quadrant → ℝ, IsFirstPassageShapeFunction μ h →
        (HasLinearLowerBound h → ∀ᵐ ω ∂environmentLaw μ,
          GrowthSetsConverge (firstPassageGrowthSet ω) (shapeSublevelSet h)) :=
  plain_firstPassage_growthSets_converge_iff_literal.mpr
    literal_firstPassage_growthSets_converge_holds μ hneg hpos

/-- The paper label of `firstPassage_growthSets_converge`. -/
alias theorem_5_1_ii := firstPassage_growthSets_converge

/-! ### Remark 5.1(i) -/

/-- Version A of Martin (2004), Remark 5.1(i): the statement
`LPPDifferentiability.martin_remark_5_1_i_lower` of the `Frozen` folder, copied verbatim. -/
def literal_taxicab_lower_bound_of_subadditive : Prop :=
  ∀ (h : Quadrant → ℝ)
    (_hhom : ∀ (c : ℝ≥0) (x : Quadrant), h (c * x.1, c * x.2) = (c : ℝ) * h x)
    (_hsymm : ∀ x : Quadrant, h (x.2, x.1) = h x)
    (_hsub : ∀ x y : Quadrant, h (x.1 + y.1, x.2 + y.2) ≤ h x + h y)
    (x : Quadrant),
    ((x.1 : ℝ) + x.2) / 2 * h (1, 1) ≤ h x

/-- The theorem of the `Frozen` folder proves version A. -/
theorem literal_taxicab_lower_bound_of_subadditive_holds : literal_taxicab_lower_bound_of_subadditive :=
  LPPDifferentiability.martin_remark_5_1_i_lower

/-- Version B of Remark 5.1(i): a homogeneous, symmetric, subadditive function `h` on the quadrant
satisfies `h x ≥ (‖x‖ / 2) h (1, 1)`. -/
def plain_taxicab_lower_bound_of_subadditive : Prop :=
  ∀ h : Quadrant → ℝ, IsHomogeneous h → IsSymmetric h → IsSubadditive h →
    ∀ x : Quadrant, taxicabNorm x / 2 * h (1, 1) ≤ h x

/-- Versions A and B are definitionally the same statement. -/
theorem plain_taxicab_lower_bound_of_subadditive_iff_literal :
    plain_taxicab_lower_bound_of_subadditive ↔ literal_taxicab_lower_bound_of_subadditive :=
  Iff.rfl

/-- Martin (2004), Remark 5.1(i) (first sentence, `d = 2`).

A homogeneous, symmetric, subadditive function `h` on the quadrant satisfies
`h x ≥ (‖x‖ / 2) h (1, 1)`. This is deterministic. -/
theorem taxicab_lower_bound_of_subadditive (h : Quadrant → ℝ) (hhom : IsHomogeneous h)
    (hsymm : IsSymmetric h) (hsub : IsSubadditive h) (x : Quadrant) :
    taxicabNorm x / 2 * h (1, 1) ≤ h x :=
  plain_taxicab_lower_bound_of_subadditive_iff_literal.mpr literal_taxicab_lower_bound_of_subadditive_holds
    h hhom hsymm hsub x

/-- The paper label of `taxicab_lower_bound_of_subadditive`. -/
alias remark_5_1_i := taxicab_lower_bound_of_subadditive

end LPPStatements.Martin2004
