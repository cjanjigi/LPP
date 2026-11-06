/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Expectation comparison from stochastic upper tails

This supplies the signed first-moment detail in Liggett's stochastic-order
argument. Positive and negative parts are compared separately by layer cake.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LPPDifferentiability

private theorem lintegral_ofReal_eq_closed_tails {α : Type*} [MeasurableSpace α] (ρ : Measure α) (f : α → ℝ)
    (hf : AEMeasurable f ρ) :
    (∫⁻ w, ENNReal.ofReal (f w) ∂ρ) = ∫⁻ t in Ioi 0, ρ {w | t ≤ f w} := by
  have h := lintegral_eq_lintegral_meas_le ρ
    (Eventually.of_forall (fun w => le_max_right (f w) 0))
    (hf.max aemeasurable_const)
  simp only [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left (zero_le : (0 : ℝ≥0∞) ≤ _)] at h
  rw [h]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  apply congrArg ρ
  ext w
  simp only [mem_ofPred_eq, le_max_iff]
  exact or_iff_left (not_le.mpr ht)

private theorem lintegral_ofReal_neg_eq_strict_lower_tails {α : Type*} [MeasurableSpace α] (ρ : Measure α) (f : α → ℝ)
    (hf : AEMeasurable f ρ) :
    (∫⁻ w, ENNReal.ofReal (-f w) ∂ρ) = ∫⁻ t in Ioi 0, ρ {w | f w < -t} := by
  have h := lintegral_eq_lintegral_meas_lt ρ
    (Eventually.of_forall (fun w => le_max_right (-f w) 0))
    (hf.neg.max aemeasurable_const)
  simp only [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left (zero_le : (0 : ℝ≥0∞) ≤ _)] at h
  rw [h]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  apply congrArg ρ
  ext w
  simp only [mem_ofPred_eq, lt_max_iff]
  rw [or_iff_left (not_lt.mpr ht.le)]
  exact lt_neg


/-- Closed upper-tail order for real integrable variables implies mean order. -/
theorem integral_le_of_closed_upper_tails
    {Ω Λ : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ]
    {μ : Measure Ω} {ν : Measure Λ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {x : Ω → ℝ} {y : Λ → ℝ} (hx : Integrable x μ) (hy : Integrable y ν)
    (htail : ∀ a : ℝ, ν {w | a ≤ y w} ≤ μ {w | a ≤ x w}) :
    (∫ w, y w ∂ν) ≤ ∫ w, x w ∂μ := by
  have hpos : (∫⁻ w, ENNReal.ofReal (y w) ∂ν) ≤
      ∫⁻ w, ENNReal.ofReal (x w) ∂μ := by
    rw [lintegral_ofReal_eq_closed_tails ν y hy.aemeasurable, lintegral_ofReal_eq_closed_tails μ x hx.aemeasurable]
    exact lintegral_mono (fun t => htail t)
  have hlower (a : ℝ) : μ {w | x w < a} ≤ ν {w | y w < a} := by
    have cx : {w | x w < a} = {w | a ≤ x w}ᶜ := by ext w; simp
    have cy : {w | y w < a} = {w | a ≤ y w}ᶜ := by ext w; simp
    rw [cx, cy, measure_compl₀ (nullMeasurableSet_le aemeasurable_const hx.aemeasurable)
      (measure_ne_top _ _), measure_compl₀
      (nullMeasurableSet_le aemeasurable_const hy.aemeasurable) (measure_ne_top _ _)]
    simpa only [measure_univ] using tsub_le_tsub_left (htail a) 1
  have hneg : (∫⁻ w, ENNReal.ofReal (-x w) ∂μ) ≤
      ∫⁻ w, ENNReal.ofReal (-y w) ∂ν := by
    rw [lintegral_ofReal_neg_eq_strict_lower_tails μ x hx.aemeasurable,
      lintegral_ofReal_neg_eq_strict_lower_tails ν y hy.aemeasurable]
    exact lintegral_mono (fun t => hlower (-t))
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hy,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hx]
  exact sub_le_sub (ENNReal.toReal_mono hx.lintegral_lt_top.ne hpos)
    (ENNReal.toReal_mono hy.neg.lintegral_lt_top.ne hneg)

end LPPDifferentiability
