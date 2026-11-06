/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Analysis.BernsteinExpBound
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Centered exponential moments of a bounded variable

The mean, variance and integrability are those of the actual variable.
-/

public section

open MeasureTheory ProbabilityTheory

namespace LPPDifferentiability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {Z : Ω → ℝ} {b : ℝ}

/-- A measurable variable between zero and a finite bound has every finite moment. -/
theorem memLp_of_ae_nonneg_le (hZ : Measurable Z)
    (hbound : ∀ᵐ ω ∂P, 0 ≤ Z ω ∧ Z ω ≤ b) (p : ENNReal) : MemLp Z p P :=
  memLp_of_bounded hbound hZ.aestronglyMeasurable p

/-- The actual mean inherits the almost-everywhere interval bounds. -/
theorem integral_nonneg_le_of_ae_bounded (hZ : Measurable Z)
    (hbound : ∀ᵐ ω ∂P, 0 ≤ Z ω ∧ Z ω ≤ b) :
    0 ≤ ∫ ω, Z ω ∂P ∧ (∫ ω, Z ω ∂P) ≤ b := by
  have hi := (memLp_of_ae_nonneg_le hZ hbound 1).integrable (by norm_num)
  constructor
  · exact integral_nonneg_of_ae (hbound.mono fun _ h => h.1)
  · have h := integral_mono_ae hi (integrable_const b) (hbound.mono fun _ h => h.2)
    simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using h

/-- Centering a variable in `[0,b]` gives absolute bound `b`. -/
theorem ae_abs_centered_le (hZ : Measurable Z)
    (hbound : ∀ᵐ ω ∂P, 0 ≤ Z ω ∧ Z ω ≤ b) :
    ∀ᵐ ω ∂P, |Z ω - ∫ x, Z x ∂P| ≤ b := by
  obtain ⟨hm₀, hmb⟩ := integral_nonneg_le_of_ae_bounded hZ hbound
  filter_upwards [hbound] with ω hω
  exact abs_le.mpr ⟨by linarith only [hω.1, hmb], by linarith only [hω.2, hm₀]⟩

/-- Boundedness supplies exponential integrability for every real parameter. -/
theorem integrable_exp_centered_of_ae_bounded (hZ : Measurable Z)
    (hbound : ∀ᵐ ω ∂P, 0 ≤ Z ω ∧ Z ω ≤ b) (lam : ℝ) :
    Integrable (fun ω => Real.exp (lam * (Z ω - ∫ x, Z x ∂P))) P := by
  apply (MemLp.of_bound (p := 1)
    (((hZ.sub_const _).const_mul lam).exp.aestronglyMeasurable)
    (Real.exp (|lam| * b)) ?_).integrable (by norm_num)
  filter_upwards [ae_abs_centered_le hZ hbound] with ω hω
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    lam * (Z ω - ∫ x, Z x ∂P) ≤ |lam * (Z ω - ∫ x, Z x ∂P)| := le_abs_self _
    _ = |lam| * |Z ω - ∫ x, Z x ∂P| := abs_mul _ _
    _ ≤ |lam| * b := mul_le_mul_of_nonneg_left hω (abs_nonneg _)

/-- The exact one-variable Bernstein MGF bound with actual variance. -/
theorem bernstein_mgf_centered (hZ : Measurable Z)
    (hb : 0 < b) (hbound : ∀ᵐ ω ∂P, 0 ≤ Z ω ∧ Z ω ≤ b)
    (lam : ℝ) (hlam : 0 ≤ lam) (hsmall : lam * b < 3) :
    mgf (fun ω => Z ω - ∫ x, Z x ∂P) P lam ≤
      Real.exp (lam ^ 2 * Var[Z; P] / (2 * (1 - lam * b / 3))) := by
  have hLp : MemLp Z 2 P := memLp_of_ae_nonneg_le hZ hbound 2
  have hi : Integrable Z P := hLp.integrable (by norm_num)
  have hc : Integrable (fun ω => Z ω - ∫ x, Z x ∂P) P :=
    hi.sub (integrable_const _)
  have hcsq : Integrable (fun ω => (Z ω - ∫ x, Z x ∂P) ^ 2) P :=
    (hLp.sub (memLp_const _)).integrable_sq
  have hzero : (∫ ω, (Z ω - ∫ x, Z x ∂P) ∂P) = 0 := by
    rw [integral_sub hi (integrable_const _)]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, sub_self]
  have hlin : Integrable (fun ω => 1 + lam * (Z ω - ∫ x, Z x ∂P)) P :=
    (integrable_const 1).add (hc.const_mul lam)
  have hquad : Integrable (fun ω =>
      lam ^ 2 * (Z ω - ∫ x, Z x ∂P) ^ 2 / (2 * (1 - lam * b / 3))) P :=
    (hcsq.const_mul (lam ^ 2)).div_const _
  have hmajor := integral_mono_ae
    (integrable_exp_centered_of_ae_bounded hZ hbound lam)
    (hlin.add hquad)
    ((ae_abs_centered_le hZ hbound).mono fun ω hω =>
      exp_mul_le_one_add_add_sq_div b lam _ hb hlam hsmall hω)
  have heq : (∫ ω, (1 + lam * (Z ω - ∫ x, Z x ∂P) +
      lam ^ 2 * (Z ω - ∫ x, Z x ∂P) ^ 2 / (2 * (1 - lam * b / 3))) ∂P) =
      1 + lam ^ 2 * Var[Z; P] / (2 * (1 - lam * b / 3)) := by
    rw [integral_add hlin hquad,
      integral_add (integrable_const 1) (hc.const_mul lam),
      integral_const, probReal_univ, smul_eq_mul, one_mul,
      integral_const_mul, hzero, mul_zero, add_zero,
      integral_div, integral_const_mul, ← variance_eq_integral hZ.aemeasurable]
  change (∫ ω, Real.exp (lam * (Z ω - ∫ x, Z x ∂P)) ∂P) ≤ _
  simp only [Pi.add_apply] at hmajor
  rw [heq] at hmajor
  exact hmajor.trans (by simpa only [add_comm] using (Real.add_one_le_exp
    (lam ^ 2 * Var[Z; P] / (2 * (1 - lam * b / 3)))))

end LPPDifferentiability
