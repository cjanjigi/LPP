/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.BernsteinSumMGF
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Bernstein's inequality with the actual finite variance sum

The zero-variance case uses a strictly interior exponential parameter.
The second-moment corollary is the denominator estimate used in the weights lemma.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace LPPDifferentiability

variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
  {P : Measure Ω} [IsProbabilityMeasure P] {Z : I → Ω → ℝ} {b : ℝ}

/-- Exponential Markov applied to the actual centered sum. -/
theorem bernstein_chernoff (hZ : ∀ i, Measurable (Z i))
    (hind : iIndepFun Z P) (hb : 0 < b)
    (hbound : ∀ i, ∀ᵐ ω ∂P, 0 ≤ Z i ω ∧ Z i ω ≤ b)
    (t lam : ℝ) (hlam : 0 ≤ lam) (hsmall : lam * b < 3) :
    P.real {ω | (∑ i, Z i ω) > (∑ i, ∫ x, Z i x ∂P) + t} ≤
      Real.exp (-lam * t + lam ^ 2 * (∑ i, Var[Z i; P]) /
        (2 * (1 - lam * b / 3))) := by
  have hevent : {ω | (∑ i, Z i ω) > (∑ i, ∫ x, Z i x ∂P) + t} ⊆
      {ω | t ≤ ∑ i, (Z i ω - ∫ x, Z i x ∂P)} := by
    intro ω hω
    change (∑ i, Z i ω) > (∑ i, ∫ x, Z i x ∂P) + t at hω
    change t ≤ ∑ i, (Z i ω - ∫ x, Z i x ∂P)
    rw [Finset.sum_sub_distrib]
    linarith only [hω]
  calc
    P.real {ω | (∑ i, Z i ω) > (∑ i, ∫ x, Z i x ∂P) + t} ≤
        P.real {ω | t ≤ ∑ i, (Z i ω - ∫ x, Z i x ∂P)} := measureReal_mono hevent
    _ ≤ Real.exp (-lam * t) *
        mgf (fun ω => ∑ i, (Z i ω - ∫ x, Z i x ∂P)) P lam :=
      measure_ge_le_exp_mul_mgf t hlam (integrable_exp_centered_sum hZ hind hbound lam)
    _ ≤ Real.exp (-lam * t) *
        Real.exp (lam ^ 2 * (∑ i, Var[Z i; P]) / (2 * (1 - lam * b / 3))) :=
      mul_le_mul_of_nonneg_left (bernstein_mgf_centered_sum hZ hind hb hbound lam hlam hsmall)
        (Real.exp_nonneg _)
    _ = _ := (Real.exp_add _ _).symm

/-- Bernstein's exact upper tail, with no positive-variance or nonempty-index assumption. -/
theorem bernstein_upper_tail (hZ : ∀ i, Measurable (Z i))
    (hind : iIndepFun Z P) (hb : 0 < b)
    (hbound : ∀ i, ∀ᵐ ω ∂P, 0 ≤ Z i ω ∧ Z i ω ≤ b)
    (t : ℝ) (ht : 0 < t) :
    P.real {ω | (∑ i, Z i ω) > (∑ i, ∫ x, Z i x ∂P) + t} ≤
      Real.exp (-t ^ 2 / (2 * ((∑ i, Var[Z i; P]) + b * t / 3))) := by
  let v : ℝ := ∑ i, Var[Z i; P]
  have hv : 0 ≤ v := Finset.sum_nonneg fun i _ => variance_nonneg (Z i) P
  change _ ≤ Real.exp (-t ^ 2 / (2 * (v + b * t / 3)))
  by_cases hv0 : v = 0
  · let lam : ℝ := 3 / (2 * b)
    have hlam : 0 ≤ lam := by dsimp [lam]; positivity
    have hmul : lam * b = 3 / 2 := by dsimp [lam]; field_simp [hb.ne']
    have hsmall : lam * b < 3 := by rw [hmul]; norm_num
    have h := bernstein_chernoff hZ hind hb hbound t lam hlam hsmall
    change _ ≤ Real.exp (-lam * t + lam ^ 2 * v / (2 * (1 - lam * b / 3))) at h
    rw [hv0, mul_zero, zero_div, add_zero] at h
    have heq : -lam * t = -t ^ 2 / (2 * (v + b * t / 3)) := by
      rw [hv0]
      dsimp [lam]
      field_simp [hb.ne', ht.ne']
      ring
    rwa [heq] at h
  · have hvpos : 0 < v := lt_of_le_of_ne hv (Ne.symm hv0)
    let d : ℝ := v + b * t / 3
    have hd : 0 < d := by dsimp [d]; positivity
    let lam : ℝ := t / d
    have hlam : 0 ≤ lam := by dsimp [lam]; positivity
    have hsmall : lam * b < 3 := by
      dsimp [lam]
      rw [div_mul_eq_mul_div, div_lt_iff₀ hd]
      dsimp [d]
      nlinarith only [hvpos]
    have h := bernstein_chernoff hZ hind hb hbound t lam hlam hsmall
    change _ ≤ Real.exp (-lam * t + lam ^ 2 * v / (2 * (1 - lam * b / 3))) at h
    have hden : 1 - lam * b / 3 = v / d := by
      dsimp [lam]
      field_simp [hd.ne']
      dsimp [d]
      ring
    have heq : -lam * t + lam ^ 2 * v / (2 * (1 - lam * b / 3)) =
        -t ^ 2 / (2 * (v + b * t / 3)) := by
      rw [hden]
      change -(t / d) * t + (t / d) ^ 2 * v / (2 * (v / d)) = -t ^ 2 / (2 * d)
      field_simp [hd.ne', hvpos.ne']
      ring
    rwa [heq] at h

/-- Actual second moments imply the source denominator `2*b*(2*C₁*n+t/3)`. -/
theorem bernstein_upper_tail_of_second_moment_sum_le
    (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z P) (hb : 0 < b)
    (hbound : ∀ i, ∀ᵐ ω ∂P, 0 ≤ Z i ω ∧ Z i ω ≤ b)
    (C₁ : ℝ) (n : ℕ)
    (hsecond : (∑ i, ∫ ω, (Z i ω) ^ 2 ∂P) ≤ 2 * C₁ * n * b)
    (t : ℝ) (ht : 0 < t) :
    P.real {ω | (∑ i, Z i ω) > (∑ i, ∫ x, Z i x ∂P) + t} ≤
      Real.exp (-t ^ 2 / (2 * b * (2 * C₁ * n + t / 3))) := by
  have hv : 0 ≤ ∑ i, Var[Z i; P] := Finset.sum_nonneg fun i _ => variance_nonneg (Z i) P
  have hvsecond : (∑ i, Var[Z i; P]) ≤ ∑ i, ∫ ω, (Z i ω) ^ 2 ∂P := by
    apply Finset.sum_le_sum
    intro i _
    exact variance_le_expectation_sq (hZ i).aestronglyMeasurable
  have hvcap := hvsecond.trans hsecond
  have hd : 0 < 2 * ((∑ i, Var[Z i; P]) + b * t / 3) := by positivity
  have hden : 2 * ((∑ i, Var[Z i; P]) + b * t / 3) ≤
      2 * b * (2 * C₁ * n + t / 3) := by nlinarith only [hvcap]
  apply (bernstein_upper_tail hZ hind hb hbound t ht).trans
  apply Real.exp_le_exp.mpr
  simpa only [neg_div] using
    neg_le_neg (div_le_div_of_nonneg_left (sq_nonneg t) hd hden)

end LPPDifferentiability
