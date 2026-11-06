/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.LastPassage.Axes
public import LPP_Foundations.Probability.PassageIntegrable

/-!
# Axis passage means

Under an integrable one-site probability law, the mean passage time along each
coordinate axis is its length times the one-site mean.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace LPPDifferentiability

/-- The mean actual horizontal passage is its length times the marginal mean. -/
theorem integral_lastPassage_horizontal (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) (u : Lattice) (n : ℕ) :
    (∫ ω : Environment, lastPassage ω u (n, 0) ∂environmentLaw μ) =
      n * ∫ x : ℝ, x ∂μ := by
  simp_rw [lastPassage_horizontal]
  rw [integral_finsetSum Finset.univ
    (fun i _ => integrable_environment_eval μ hμ (u.1 + (i.val : ℤ), u.2))]
  simp only [integral_environment_eval μ hμ, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

/-- The mean actual vertical passage is its length times the marginal mean. -/
theorem integral_lastPassage_vertical (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) (u : Lattice) (n : ℕ) :
    (∫ ω : Environment, lastPassage ω u (0, n) ∂environmentLaw μ) =
      n * ∫ x : ℝ, x ∂μ := by
  simp_rw [lastPassage_vertical]
  rw [integral_finsetSum Finset.univ
    (fun i _ => integrable_environment_eval μ hμ (u.1, u.2 + (i.val : ℤ)))]
  simp only [integral_environment_eval μ hμ, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

end LPPDifferentiability
