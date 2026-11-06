/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import LPP_Foundations.Frozen.Model.FirstPassage
public import LPP_Foundations.Frozen.Model.LastPassage
public import LPP_Foundations.Frozen.Model.Quadrant
public import LPP_Foundations.Model.LastPassage.FirstPassage
public import Martin2004.Probability.NegatedLaw
public import Martin2004.Shape.FirstPassageShape

/-!
# The first-passage shape as minus the shape of the negated law

Martin (2004), the remark after Theorem 2.4, (2.9) and Corollary 2.5(ii). Replacing the maximum by
a minimum and each weight `X(z)` by `-X(z)` only changes the sign of the passage time and so of the
shape. This file states that, if `g` has the four properties of the shape of the negated law
`μ.map Neg.neg` (continuous, homogeneous, concave, and the almost-sure last-passage closeness), then
`-g` has the four properties of the first-passage shape of `μ` (continuous, homogeneous, convex, and
the almost-sure first-passage closeness). It is the form of the sign change that the proof of
Corollary 2.5(ii) needs in order to identify the first-passage shape `h` with `-g`.
-/

public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace LPPDifferentiability

/-- Almost-sure closeness transfers through the sign change: if the last-passage time of the negated
environment is within `ε ‖z‖` of `g z` for all long `z`, then the first-passage time of the original
environment is within `ε ‖z‖` of `-g z`. See Martin (2004), the remark after Theorem 2.4 (the sign
change) and (2.9). -/
theorem ae_firstPassage_approx_of_negated_lastPassage (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (g : Quadrant → ℝ)
    (hae : ∀ᵐ ω ∂environmentLaw (μ.map Neg.neg),
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ z : ℕ × ℕ,
        N ≤ z.1 + z.2 →
        |lastPassage ω (0, 0) z - g ((z.1 : ℝ≥0), (z.2 : ℝ≥0))| ≤
          ε * ((z.1 + z.2 : ℕ) : ℝ)) :
    ∀ᵐ ω ∂environmentLaw μ,
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ z : ℕ × ℕ,
        N ≤ z.1 + z.2 →
        |firstPassage ω (0, 0) z - (-g ((z.1 : ℝ≥0), (z.2 : ℝ≥0)))| ≤
          ε * ((z.1 + z.2 : ℕ) : ℝ) := by
  -- Negating the environment carries the almost-sure event of the negated law to the original law.
  have hneg := (ae_environmentLaw_negated_iff μ _).1 hae
  filter_upwards [hneg] with ω hω ε hε
  obtain ⟨N, hN⟩ := hω ε hε
  refine ⟨N, fun z hz => ?_⟩
  -- The two absolute errors are equal, because first passage is minus last passage of `-ω`.
  have key : |firstPassage ω (0, 0) z - (-g ((z.1 : ℝ≥0), (z.2 : ℝ≥0)))| =
      |lastPassage (-ω) (0, 0) z - g ((z.1 : ℝ≥0), (z.2 : ℝ≥0))| := by
    rw [firstPassage_eq_neg_lastPassage ω (0, 0) z]
    exact abs_eq_abs.2 (Or.inr (by ring))
  rw [key]
  exact hN z hz

/-- See Martin (2004), the remark after Theorem 2.4. The four properties of a shape `g` of the
negated law give the four properties of the first-passage shape `-g` of `μ`: continuity,
homogeneity, convexity (the negation of concavity) and almost-sure first-passage closeness. -/
theorem firstPassage_shape_clauses_of_negated_shape (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (g : Quadrant → ℝ)
    (hg : Continuous g ∧
      (∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x) ∧
      (∀ (x y : Quadrant) (a b : ℝ≥0), a + b = 1 →
        (a : ℝ) * g x + (b : ℝ) * g y ≤ g (a * x.1 + b * y.1, a * x.2 + b * y.2)) ∧
      (∀ᵐ ω ∂environmentLaw (μ.map Neg.neg),
        ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ z : ℕ × ℕ,
          N ≤ z.1 + z.2 →
          |lastPassage ω (0, 0) z - g ((z.1 : ℝ≥0), (z.2 : ℝ≥0))| ≤
            ε * ((z.1 + z.2 : ℕ) : ℝ))) :
    Continuous (fun x : Quadrant => -g x) ∧
      (∀ (c : ℝ≥0) (x : Quadrant),
        (fun x : Quadrant => -g x) (c * x.1, c * x.2) = (c : ℝ) * (fun x : Quadrant => -g x) x) ∧
      (∀ (x y : Quadrant) (a b : ℝ≥0), a + b = 1 →
        (fun x : Quadrant => -g x) (a * x.1 + b * y.1, a * x.2 + b * y.2) ≤
          (a : ℝ) * (fun x : Quadrant => -g x) x + (b : ℝ) * (fun x : Quadrant => -g x) y) ∧
      (∀ᵐ ω ∂environmentLaw μ,
        ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ z : ℕ × ℕ,
          N ≤ z.1 + z.2 →
          |firstPassage ω (0, 0) z - (fun x : Quadrant => -g x) ((z.1 : ℝ≥0), (z.2 : ℝ≥0))| ≤
            ε * ((z.1 + z.2 : ℕ) : ℝ)) := by
  obtain ⟨hcont, hhom, hconc, hae⟩ := hg
  refine ⟨hcont.neg, ?_, ?_, ae_firstPassage_approx_of_negated_lastPassage μ g hae⟩
  · -- Homogeneity.
    intro c x
    show -g (c * x.1, c * x.2) = (c : ℝ) * -g x
    rw [hhom c x, mul_neg]
  · -- Convexity is concavity of `g`, negated.
    intro x y a b hab
    have h2 := hconc x y a b hab
    show -g (a * x.1 + b * y.1, a * x.2 + b * y.2) ≤ (a : ℝ) * -g x + (b : ℝ) * -g y
    linarith only [h2]

end LPPDifferentiability
