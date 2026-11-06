/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Positive moments and integrated square-root tails

The positive moment assumption in the full paper implies the positive
integrated square-root tail condition by Markov's inequality. The elementary
argument requires only an exponent greater than two and allows signed laws
and atoms. It supplies no assertion about the negative tail.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LPPDifferentiability

/-- A finite lower integral of the positive power gives actual integrability. -/
theorem integrable_positive_rpow_of_lintegral_lt_top
    (μ : Measure ℝ) {p : ℝ} (hp : 0 < p)
    (hmoment : (∫⁻ x, ENNReal.ofReal ((max x 0) ^ p) ∂μ) < ∞) :
    Integrable (fun x : ℝ => (max x 0) ^ p) μ := by
  refine (lintegral_ofReal_ne_top_iff_integrable ?_ ?_).mp hmoment.ne
  · exact ((Real.continuous_rpow_const hp.le).comp
      (continuous_id.max continuous_const)).measurable.aestronglyMeasurable
  · exact Eventually.of_forall fun x => Real.rpow_nonneg (le_max_right x 0) p

/-- Markov's inequality for the actual positive part of a signed real law. -/
theorem positive_tail_le_moment_div_rpow
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {p : ℝ} (hp : 0 < p)
    (hmoment : (∫⁻ x, ENNReal.ofReal ((max x 0) ^ p) ∂μ) < ∞)
    {t : ℝ} (ht : 0 < t) :
    μ.real (Ioi t) ≤ (∫ x : ℝ, (max x 0) ^ p ∂μ) / t ^ p := by
  have hi := integrable_positive_rpow_of_lintegral_lt_top μ hp hmoment
  have hsub : Ioi t ⊆ {x : ℝ | t ^ p ≤ (max x 0) ^ p} := by
    intro x hx
    exact Real.rpow_le_rpow ht.le (hx.le.trans (le_max_left x 0)) hp.le
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall fun x : ℝ => Real.rpow_nonneg (le_max_right x 0) p) hi (t ^ p)
  apply (le_div_iff₀ (Real.rpow_pos_of_pos ht p)).2
  calc
    μ.real (Ioi t) * t ^ p = t ^ p * μ.real (Ioi t) := mul_comm _ _
    _ ≤ t ^ p * μ.real {x : ℝ | t ^ p ≤ (max x 0) ^ p} :=
      mul_le_mul_of_nonneg_left (measureReal_mono hsub) (Real.rpow_nonneg ht.le p)
    _ ≤ _ := hm

/-- Any finite positive real-power moment of order greater than two gives
the literal positive integrated square-root tail condition. -/
theorem positive_integrated_sqrt_tail_lt_top_of_moment
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {p : ℝ} (hp : 2 < p)
    (hmoment : (∫⁻ x, ENNReal.ofReal ((max x 0) ^ p) ∂μ) < ∞) :
    (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞ := by
  have hp0 : 0 < p := lt_trans (by norm_num) hp
  let M : ℝ := ∫ x : ℝ, (max x 0) ^ p ∂μ
  have hM : 0 ≤ M := integral_nonneg fun x => Real.rpow_nonneg (le_max_right x 0) p
  have htailanti : Antitone (fun t : ℝ => μ.real (Ioi t)) := by
    intro a b hab
    exact measureReal_mono (Ioi_subset_Ioi hab)
  have hfmeas : Measurable (fun t : ℝ => (μ.real (Ioi t)) ^ (1 / 2 : ℝ)) :=
    (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 2)).measurable.comp
      htailanti.measurable
  have hf0 (t : ℝ) : 0 ≤ (μ.real (Ioi t)) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg measureReal_nonneg _
  have hbound (t : ℝ) (ht : 0 < t) :
      (μ.real (Ioi t)) ^ (1 / 2 : ℝ) ≤ M ^ (1 / 2 : ℝ) * t ^ (-p / 2) := by
    calc
      (μ.real (Ioi t)) ^ (1 / 2 : ℝ) ≤ (M / t ^ p) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow measureReal_nonneg
          (positive_tail_le_moment_div_rpow μ hp0 hmoment ht) (by norm_num)
      _ = M ^ (1 / 2 : ℝ) * t ^ (-p / 2) := by
        rw [Real.div_rpow hM (Real.rpow_nonneg ht.le p),
          ← Real.rpow_mul ht.le, div_eq_mul_inv, ← Real.rpow_neg ht.le]
        congr 2
        ring
  have hsmall : IntegrableOn (fun t : ℝ => (μ.real (Ioi t)) ^ (1 / 2 : ℝ))
      (Ioc 0 1) := by
    have hc : Integrable (fun _ : ℝ => (1 : ℝ))
        (volume.restrict (Ioc (0 : ℝ) 1)) :=
      (integrableOn_const (μ := volume) (s := Ioc (0 : ℝ) 1)
        (C := (1 : ℝ)) (by simp)).integrable
    change Integrable _ (volume.restrict (Ioc (0 : ℝ) 1))
    apply hc.mono' hfmeas.aestronglyMeasurable.restrict
    exact Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 t)]
      simpa only [Real.one_rpow] using
        (Real.rpow_le_rpow measureReal_nonneg measureReal_le_one
          (by norm_num : (0 : ℝ) ≤ 1 / 2))
  have hlarge : IntegrableOn (fun t : ℝ => (μ.real (Ioi t)) ^ (1 / 2 : ℝ))
      (Ioi 1) := by
    have hpow : IntegrableOn (fun t : ℝ => t ^ (-p / 2)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith only [hp]) zero_lt_one
    apply (hpow.const_mul (M ^ (1 / 2 : ℝ))).mono'
      hfmeas.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 t)]
    exact hbound t (lt_trans zero_lt_one ht)
  have hfull : IntegrableOn (fun t : ℝ => (μ.real (Ioi t)) ^ (1 / 2 : ℝ))
      (Ioi 0) := by
    simpa only [Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)] using hsmall.union hlarge
  have hfinite := (hasFiniteIntegral_iff_ofReal
    (Eventually.of_forall hf0)).mp hfull.hasFiniteIntegral
  convert hfinite using 1
  apply lintegral_congr
  intro t
  rw [measureReal_def, ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg
    (by norm_num : (0 : ℝ) ≤ 1 / 2), ENNReal.ofReal_toReal (measure_ne_top μ (Ioi t))]

/-- Direct consumer of the full paper's exact positive moment premise. -/
theorem positive_integrated_sqrt_tail_lt_top_of_full_positive_moment
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hpos : ∃ p : ℝ, 4 < p ∧
      (∫⁻ x, ENNReal.ofReal ((max x 0) ^ p) ∂μ) < ∞) :
    (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞ := by
  obtain ⟨p, hp, hmoment⟩ := hpos
  exact positive_integrated_sqrt_tail_lt_top_of_moment μ
    (lt_trans (by norm_num) hp) hmoment

end LPPDifferentiability
