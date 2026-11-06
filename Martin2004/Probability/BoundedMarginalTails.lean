/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.MeasureTheory.Integral.Layercake

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import LPP_Foundations.Probability.PassageMeanBounds

/-!
# Martin's integrated square-root tails under bounded marginals

An almost surely bounded real marginal has a finite mean and both integrated
Martin square-root tails are bounded by the same support radius. The negative
tail keeps its closed event, including a possible atom at the left endpoint.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace LPPDifferentiability

private theorem measure_rpow_half_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (s : Set ℝ) : (μ s) ^ (1 / 2 : ℝ) ≤ 1 := by
  have hs : μ s ≤ 1 := by
    calc
      μ s ≤ μ Set.univ := measure_mono (Set.subset_univ s)
      _ = 1 := measure_univ
  calc
    (μ s) ^ (1 / 2 : ℝ) ≤ (1 : ℝ≥0∞) ^ (1 / 2 : ℝ) :=
      ENNReal.rpow_le_rpow hs (by norm_num)
    _ = 1 := by rw [ENNReal.one_rpow]

private theorem measure_Iic_eq_zero_of_ae_abs_le (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (L : ℝ) (hL : 0 ≤ L)
    (hμ : ∀ᵐ x ∂μ, |x| ≤ L) (t : ℝ) (ht : t < -L) : μ (Iic t) = 0 := by
  have hbad : μ {x : ℝ | L < |x|} = 0 := by
    simpa only [not_le] using (ae_iff.mp hμ)
  apply measure_mono_null (s := Iic t) (t := {x : ℝ | L < |x|})
  · intro x hx
    simp only [mem_Iic] at hx
    change L < |x|
    have ht0 : t < 0 := lt_of_lt_of_le ht (neg_nonpos.mpr hL)
    have hx0 : x < 0 := lt_of_le_of_lt hx ht0
    rw [abs_of_neg hx0]
    linarith
  · exact hbad

private theorem measure_Ioi_eq_zero_of_ae_abs_le (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (L : ℝ) (hL : 0 ≤ L)
    (hμ : ∀ᵐ x ∂μ, |x| ≤ L) (t : ℝ) (ht : L ≤ t) : μ (Ioi t) = 0 := by
  have hbad : μ {x : ℝ | L < |x|} = 0 := by
    simpa only [not_le] using (ae_iff.mp hμ)
  apply measure_mono_null (s := Ioi t) (t := {x : ℝ | L < |x|})
  · intro x hx
    simp only [mem_Ioi] at hx
    change L < |x|
    have hx0 : 0 < x := lt_of_le_of_lt hL (lt_of_le_of_lt ht hx)
    rw [abs_of_pos hx0]
    linarith
  · exact hbad

/-- A bounded probability law has an integrable identity function and a mean
whose absolute value is at most the same bound. -/
theorem abs_integral_id_le_of_ae_abs_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (L : ℝ) (_hL : 0 ≤ L) (hμ : ∀ᵐ x ∂μ, |x| ≤ L) :
    |∫ x : ℝ, x ∂μ| ≤ L := by
  have hμ_int := integrable_id_of_ae_abs_le μ L hμ
  have hnorm : ∫ x : ℝ, |x| ∂μ ≤ L := by
    calc
      ∫ x : ℝ, |x| ∂μ ≤ ∫ _x : ℝ, L ∂μ :=
        integral_mono_ae hμ_int.abs (integrable_const L) (by
          filter_upwards [hμ] with x hx
          exact hx)
      _ = L := by simp
  exact (abs_integral_le_integral_abs.trans hnorm)

/-- The closed negative Martin square-root tail of a bounded probability law
is at most the support radius. The closed event retains a possible atom at
`-L`; only the single integration point is negligible. -/
theorem integrated_negative_sqrt_tail_le_of_ae_abs_le (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (L : ℝ) (hL : 0 ≤ L)
    (hμ : ∀ᵐ x ∂μ, |x| ≤ L) :
    (∫⁻ t in Iio (0 : ℝ), (μ (Iic t)) ^ (1 / 2 : ℝ)) ≤ ENNReal.ofReal L := by
  have hdom : ∀ t ∈ Iio (0 : ℝ),
      (μ (Iic t)) ^ (1 / 2 : ℝ) ≤ (Icc (-L) 0).indicator (fun _ : ℝ => (1 : ℝ≥0∞)) t := by
    intro t ht
    by_cases hmem : t ∈ Icc (-L) 0
    · simpa only [Set.indicator_of_mem hmem] using
        (measure_rpow_half_le_one μ (Iic t))
    · have htlow : t < -L := by
        by_contra hnot
        exact hmem ⟨le_of_not_gt hnot, le_of_lt ht⟩
      rw [Set.indicator_of_notMem hmem,
        measure_Iic_eq_zero_of_ae_abs_le μ L hL hμ t htlow,
        ENNReal.zero_rpow_of_pos (by norm_num : 0 < (1 / 2 : ℝ))]
  calc
    (∫⁻ t in Iio (0 : ℝ), (μ (Iic t)) ^ (1 / 2 : ℝ)) ≤
        ∫⁻ t in Iio (0 : ℝ), (Icc (-L) 0).indicator
          (fun _ : ℝ => (1 : ℝ≥0∞)) t :=
      setLIntegral_mono' measurableSet_Iio hdom
    _ ≤ ∫⁻ t : ℝ, (Icc (-L) 0).indicator (fun _ => (1 : ℝ≥0∞)) t ∂volume :=
      lintegral_mono' Measure.restrict_le_self le_rfl
    _ = volume (Icc (-L) 0) := by
      rw [lintegral_indicator_const measurableSet_Icc]
      simp
    _ = ENNReal.ofReal L := by
      rw [Real.volume_Icc]
      congr 1
      linarith

/-- The strict positive Martin square-root tail of a bounded probability law
is at most the support radius. -/
theorem integrated_positive_sqrt_tail_le_of_ae_abs_le (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (L : ℝ) (hL : 0 ≤ L)
    (hμ : ∀ᵐ x ∂μ, |x| ≤ L) :
    (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) ≤ ENNReal.ofReal L := by
  have hdom : ∀ t ∈ Ioi (0 : ℝ),
      (μ (Ioi t)) ^ (1 / 2 : ℝ) ≤ (Icc 0 L).indicator (fun _ : ℝ => (1 : ℝ≥0∞)) t := by
    intro t ht
    by_cases hmem : t ∈ Icc 0 L
    · simpa only [Set.indicator_of_mem hmem] using
        (measure_rpow_half_le_one μ (Ioi t))
    · have htlarge : L ≤ t := by
        by_contra hnot
        exact hmem ⟨le_of_lt ht, le_of_lt (lt_of_not_ge hnot)⟩
      rw [Set.indicator_of_notMem hmem,
        measure_Ioi_eq_zero_of_ae_abs_le μ L hL hμ t htlarge,
        ENNReal.zero_rpow_of_pos (by norm_num : 0 < (1 / 2 : ℝ))]
  calc
    (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) ≤
        ∫⁻ t in Ioi (0 : ℝ), (Icc 0 L).indicator
          (fun _ : ℝ => (1 : ℝ≥0∞)) t :=
      setLIntegral_mono' measurableSet_Ioi hdom
    _ ≤ ∫⁻ t : ℝ, (Icc 0 L).indicator (fun _ => (1 : ℝ≥0∞)) t ∂volume :=
      lintegral_mono' Measure.restrict_le_self le_rfl
    _ = volume (Icc 0 L) := by
      rw [lintegral_indicator_const measurableSet_Icc]
      simp
    _ = ENNReal.ofReal L := by
      rw [Real.volume_Icc]
      congr 1
      linarith

end LPPDifferentiability
