/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.BernsteinMGF
import Mathlib.Tactic.Ring

/-!
# The actual finite independent sum exponential moment
-/

public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace LPPDifferentiability

variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
  {P : Measure Ω} [IsProbabilityMeasure P] {Z : I → Ω → ℝ} {b : ℝ}

omit [Fintype I] [IsProbabilityMeasure P] in
/-- Deterministic centering preserves independence of the actual variables. -/
theorem iIndepFun_centered (hind : iIndepFun Z P) :
    iIndepFun (fun i ω => Z i ω - ∫ x, Z i x ∂P) P :=
  hind.comp (fun i x => x - ∫ ω, Z i ω ∂P) (fun _ => measurable_id.sub_const _)

/-- The centered finite sum has an integrable exponential for every parameter. -/
theorem integrable_exp_centered_sum (hZ : ∀ i, Measurable (Z i))
    (hind : iIndepFun Z P) (hbound : ∀ i, ∀ᵐ ω ∂P, 0 ≤ Z i ω ∧ Z i ω ≤ b)
    (lam : ℝ) :
    Integrable (fun ω => Real.exp (lam * (∑ i, (Z i ω - ∫ x, Z i x ∂P)))) P := by
  simpa only [Finset.sum_apply] using (iIndepFun_centered hind).integrable_exp_mul_sum
    (fun i => (hZ i).sub_const _) (s := Finset.univ)
    (fun i _ => integrable_exp_centered_of_ae_bounded (hZ i) (hbound i) lam)

omit [IsProbabilityMeasure P] in
/-- Independence gives an equality of the actual finite sum MGF with its product. -/
theorem mgf_centered_sum_eq_prod (hZ : ∀ i, Measurable (Z i))
    (hind : iIndepFun Z P) (lam : ℝ) :
    mgf (fun ω => ∑ i, (Z i ω - ∫ x, Z i x ∂P)) P lam =
      ∏ i, mgf (fun ω => Z i ω - ∫ x, Z i x ∂P) P lam := by
  have hfun : (fun ω => ∑ i, (Z i ω - ∫ x, Z i x ∂P)) =
      ∑ i, (fun ω => Z i ω - ∫ x, Z i x ∂P) := by
    funext ω
    simp only [Finset.sum_apply]
  rw [hfun]
  exact (iIndepFun_centered hind).mgf_sum (t := lam)
    (fun i => (hZ i).sub_const _) Finset.univ

/-- The exact Bernstein MGF estimate for any finite independent family. -/
theorem bernstein_mgf_centered_sum (hZ : ∀ i, Measurable (Z i))
    (hind : iIndepFun Z P) (hb : 0 < b)
    (hbound : ∀ i, ∀ᵐ ω ∂P, 0 ≤ Z i ω ∧ Z i ω ≤ b)
    (lam : ℝ) (hlam : 0 ≤ lam) (hsmall : lam * b < 3) :
    mgf (fun ω => ∑ i, (Z i ω - ∫ x, Z i x ∂P)) P lam ≤
      Real.exp (lam ^ 2 * (∑ i, Var[Z i; P]) / (2 * (1 - lam * b / 3))) := by
  rw [mgf_centered_sum_eq_prod hZ hind]
  calc
    (∏ i, mgf (fun ω => Z i ω - ∫ x, Z i x ∂P) P lam) ≤
        ∏ i, Real.exp (lam ^ 2 * Var[Z i; P] / (2 * (1 - lam * b / 3))) :=
      Finset.prod_le_prod₀ (fun _ _ => mgf_nonneg)
        (fun i _ => bernstein_mgf_centered (hZ i) hb (hbound i) lam hlam hsmall)
    _ = Real.exp (lam ^ 2 * (∑ i, Var[Z i; P]) / (2 * (1 - lam * b / 3))) := by
      rw [← Real.exp_sum]
      congr 1
      rw [← Finset.sum_div, ← Finset.mul_sum]

end LPPDifferentiability
