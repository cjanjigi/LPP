/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Probability.FirstMoment
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Negative moments of the negative part

A finite negative-part moment above order one gives a genuine first moment
and a finite moment at the smaller of the given order and two. The
centered result uses the same negative part and its Bochner expectation.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace LPPDifferentiability

/-- An exponent above one remains above one after taking its minimum with two. -/
theorem one_lt_min_p_two_of_one_lt {p : ℝ} (hp : 1 < p) : 1 < min p 2 := by
  exact lt_min hp (by norm_num)

/-- The minimum of an exponent and two is at most two. -/
theorem min_p_two_le_two (p : ℝ) : min p 2 ≤ 2 := min_le_right _ _

/-- The minimum of an exponent and two is at most the given exponent. -/
theorem min_p_two_le_exponent (p : ℝ) : min p 2 ≤ p := min_le_left _ _

/-- A finite moment of the actual negative part above order one gives its
Bochner first moment under a probability measure. -/
theorem integrable_negativePart_of_lintegral_lt_top
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (p : ℝ) (hp : 1 < p)
    (hmoment : (∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ p) ∂μ) < ∞) :
    Integrable (fun t : ℝ => max (-t) 0) μ := by
  exact integrable_of_nonneg_rpow_lintegral_lt_top μ
    (fun t : ℝ => max (-t) 0)
    (continuous_id.neg.max continuous_const)
    (fun _ => le_max_right _ _) p hp.le hmoment

/-- The given finite negative-part moment yields an integrable actual power
at the exponent `min p 2`. -/
theorem integrable_negativePart_rpow_of_lintegral_lt_top
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (p : ℝ) (hp : 1 < p)
    (hmoment : (∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ p) ∂μ) < ∞) :
    Integrable (fun t : ℝ => (max (-t) 0) ^ (min p 2)) μ := by
  have hf : Continuous (fun t : ℝ => max (-t) 0) :=
    continuous_id.neg.max continuous_const
  have hnonneg : ∀ t : ℝ, 0 ≤ max (-t) 0 := fun _ => le_max_right _ _
  have hp0 : 0 ≤ p := le_trans zero_le_one hp.le
  have hpower : Integrable (fun t : ℝ => (max (-t) 0) ^ p) μ := by
    refine ⟨(hf.rpow_const (fun _ => Or.inr hp0)).aestronglyMeasurable, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall (fun t => Real.rpow_nonneg (hnonneg t) p))).2 hmoment
  have hnorm : Integrable (fun t : ℝ => ‖max (-t) 0‖ ^ p) μ := by
    have heq : (fun t : ℝ => ‖max (-t) 0‖ ^ p) =
        (fun t : ℝ => (max (-t) 0) ^ p) := by
      funext t
      rw [Real.norm_of_nonneg (hnonneg t)]
    rw [heq]
    exact hpower
  have hr : 1 < min p 2 := one_lt_min_p_two_of_one_lt hp
  have hr0 : 0 ≤ min p 2 := le_of_lt (lt_trans zero_lt_one hr)
  have hnorm_r : Integrable (fun t : ℝ => ‖max (-t) 0‖ ^ (min p 2)) μ :=
    integrable_norm_rpow_of_le hf.aestronglyMeasurable hr0 hp0
      (min_p_two_le_exponent p) hnorm
  have heq : (fun t : ℝ => ‖max (-t) 0‖ ^ (min p 2)) =
      (fun t : ℝ => (max (-t) 0) ^ (min p 2)) := by
    funext t
    rw [Real.norm_of_nonneg (hnonneg t)]
  rw [← heq]
  exact hnorm_r

/-- The actual negative-part moment at `min p 2` has finite `ENNReal` integral. -/
theorem finite_lintegral_negativePart_rpow_of_lintegral_lt_top
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (p : ℝ) (hp : 1 < p)
    (hmoment : (∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ p) ∂μ) < ∞) :
    (∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ (min p 2)) ∂μ) < ∞ := by
  have hnonneg : ∀ t : ℝ, 0 ≤ (max (-t) 0) ^ (min p 2) :=
    fun t => Real.rpow_nonneg (le_max_right _ _) _
  exact (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall hnonneg)).1
    (integrable_negativePart_rpow_of_lintegral_lt_top μ p hp hmoment).hasFiniteIntegral

/-- The centered actual negative part has an integrable power at `min p 2`,
centered by its genuine Bochner expectation. -/
theorem integrable_centered_negativePart_rpow_of_lintegral_lt_top
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (p : ℝ) (hp : 1 < p)
    (hmoment : (∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ p) ∂μ) < ∞) :
    Integrable
      (fun t : ℝ => |max (-t) 0 - (∫ s, max (-s) 0 ∂μ)| ^ (min p 2)) μ := by
  have hY : Integrable (fun t : ℝ => max (-t) 0) μ :=
    integrable_negativePart_of_lintegral_lt_top μ p hp hmoment
  have hYpow : Integrable (fun t : ℝ => (max (-t) 0) ^ (min p 2)) μ :=
    integrable_negativePart_rpow_of_lintegral_lt_top μ p hp hmoment
  have hYnorm : Integrable (fun t : ℝ => ‖max (-t) 0‖ ^ (min p 2)) μ := by
    have heq : (fun t : ℝ => ‖max (-t) 0‖ ^ (min p 2)) =
        (fun t : ℝ => (max (-t) 0) ^ (min p 2)) := by
      funext t
      rw [Real.norm_of_nonneg (le_max_right _ _)]
    rw [heq]
    exact hYpow
  have hr : 1 < min p 2 := one_lt_min_p_two_of_one_lt hp
  have hrpos : 0 < min p 2 := lt_trans zero_lt_one hr
  have hr0 : 0 ≤ min p 2 := le_of_lt hrpos
  have hr_ne_zero : ENNReal.ofReal (min p 2) ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]
    exact hrpos
  have hr_ne_top : ENNReal.ofReal (min p 2) ≠ ∞ := ENNReal.ofReal_ne_top
  have hYnorm' :
      Integrable (fun t : ℝ => ‖max (-t) 0‖ ^ (ENNReal.ofReal (min p 2)).toReal) μ := by
    simpa only [ENNReal.toReal_ofReal hr0] using hYnorm
  have hYmem :
      MemLp (fun t : ℝ => max (-t) 0) (ENNReal.ofReal (min p 2)) μ :=
    (integrable_norm_rpow_iff hY.aestronglyMeasurable hr_ne_zero hr_ne_top).1 hYnorm'
  have hconst :
      MemLp (fun _ : ℝ => ∫ s, max (-s) 0 ∂μ) (ENNReal.ofReal (min p 2)) μ :=
    memLp_const _
  have hcenter :
      MemLp
        (fun t : ℝ => max (-t) 0 - (∫ s, max (-s) 0 ∂μ))
        (ENNReal.ofReal (min p 2)) μ :=
    hYmem.sub hconst
  have hcenter_norm :
      Integrable
        (fun t : ℝ =>
          ‖max (-t) 0 - (∫ s, max (-s) 0 ∂μ)‖ ^ (min p 2)) μ := by
    simpa only [ENNReal.toReal_ofReal hr0] using
      hcenter.integrable_norm_rpow hr_ne_zero hr_ne_top
  have heq :
      (fun t : ℝ =>
        ‖max (-t) 0 - (∫ s, max (-s) 0 ∂μ)‖ ^ (min p 2)) =
      (fun t : ℝ =>
        |max (-t) 0 - (∫ s, max (-s) 0 ∂μ)| ^ (min p 2)) := by
    funext t
    rw [Real.norm_eq_abs]
  rw [← heq]
  exact hcenter_norm

/-- The centered negative-part moment has finite `ENNReal` integral, with
centering by the genuine Bochner expectation of `max (-t) 0`. -/
theorem finite_lintegral_centered_negativePart_rpow_of_lintegral_lt_top
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (p : ℝ) (hp : 1 < p)
    (hmoment : (∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ p) ∂μ) < ∞) :
    (∫⁻ t, ENNReal.ofReal
      (|max (-t) 0 - (∫ s, max (-s) 0 ∂μ)| ^ (min p 2)) ∂μ) < ∞ := by
  have hnonneg : ∀ t : ℝ, 0 ≤
      |max (-t) 0 - (∫ s, max (-s) 0 ∂μ)| ^ (min p 2) :=
    fun t => Real.rpow_nonneg (abs_nonneg _) _
  exact (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall hnonneg)).1
    (integrable_centered_negativePart_rpow_of_lintegral_lt_top
      μ p hp hmoment).hasFiniteIntegral

end LPPDifferentiability
