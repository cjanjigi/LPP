/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Probability.TruncationLaw
public import ProbabilityBasics.Analysis.IntegralTails
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Integrated square-root tails of truncation remainders

These are the integration steps used in Martin (2004), Lemma 5.2. The negative
strict tail is bounded by the closed tail, so atoms are kept.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace LPPDifferentiability

/-- Translating the positive remainder gives exactly the original upper tail. -/
theorem positive_remainder_sqrt_tail (μ : Measure ℝ) (L : ℝ) :
    (∫⁻ t in Ioi (0 : ℝ),
      ((μ.map (fun x : ℝ => max (x - L) 0)) (Ioi t)) ^ (1 / 2 : ℝ)) =
    ∫⁻ t in Ioi L, (μ (Ioi t)) ^ (1 / 2 : ℝ) := by
  have h := (measurePreserving_add_left (volume : Measure ℝ) L).setLIntegral_comp_preimage_emb
    (MeasurableEquiv.addLeft L).measurableEmbedding
    (fun t : ℝ => (μ (Ioi t)) ^ (1 / 2 : ℝ)) (Ioi L)
  have hpre : (fun t : ℝ => L + t) ⁻¹' Ioi L = Ioi 0 := by
    ext t
    simp only [mem_preimage, mem_Ioi]
    constructor <;> intro ht <;> linarith only [ht]
  rw [hpre] at h
  rw [← h]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [map_positive_remainder_strict_tail μ L t ht.le]

/-- Reflection and translation bound the negative remainder by the closed lower tail. -/
theorem negative_remainder_sqrt_tail_le (μ : Measure ℝ) (L : ℝ) :
    (∫⁻ t in Ioi (0 : ℝ),
      ((μ.map (fun x : ℝ => max (-x - L) 0)) (Ioi t)) ^ (1 / 2 : ℝ)) ≤
    ∫⁻ t in Iio (-L), (μ (Iic t)) ^ (1 / 2 : ℝ) := by
  have h := (Measure.measurePreserving_sub_left (volume : Measure ℝ) (-L)).setLIntegral_comp_preimage_emb
    (MeasurableEquiv.subLeft (-L)).measurableEmbedding
    (fun t : ℝ => (μ (Iic t)) ^ (1 / 2 : ℝ)) (Iio (-L))
  have hpre : (fun t : ℝ => -L - t) ⁻¹' Iio (-L) = Ioi 0 := by
    ext t
    simp only [mem_preimage, mem_Iio, mem_Ioi]
    constructor <;> intro ht <;> linarith only [ht]
  rw [hpre] at h
  rw [← h]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [map_negative_remainder_strict_tail μ L t ht.le]
  exact ENNReal.rpow_le_rpow (measure_mono Iio_subset_Iic_self) (by norm_num)

/-- Martin's positive square-root tail tends to zero at positive infinity. -/
theorem tendsto_martin_positive_tail_zero (μ : Measure ℝ)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞) :
    Tendsto (fun L : ℝ => ∫⁻ t in Ioi L, (μ (Ioi t)) ^ (1 / 2 : ℝ))
      atTop (𝓝 0) := by
  apply tendsto_lintegral_Ioi_zero_of_lt_top _ _ 0 hpos
  apply ENNReal.continuous_rpow_const.measurable.comp
  exact (show Antitone (fun t : ℝ => μ (Ioi t)) from
    fun _ _ h => measure_mono (Ioi_subset_Ioi h)).measurable

/-- Martin's closed negative square-root tail tends to zero at reflected positive infinity. -/
theorem tendsto_martin_negative_tail_zero (μ : Measure ℝ)
    (hneg : (∫⁻ t in Iio (0 : ℝ), (μ (Iic t)) ^ (1 / 2 : ℝ)) < ∞) :
    Tendsto (fun L : ℝ => ∫⁻ t in Iio (-L), (μ (Iic t)) ^ (1 / 2 : ℝ))
      atTop (𝓝 0) := by
  have hm : Measurable (fun t : ℝ => (μ (Iic t)) ^ (1 / 2 : ℝ)) :=
    ENNReal.continuous_rpow_const.measurable.comp
      (show Monotone (fun t : ℝ => μ (Iic t)) from
        fun _ _ h => measure_mono (Iic_subset_Iic.mpr h)).measurable
  exact (tendsto_lintegral_Iio_zero_of_lt_top _ hm 0 hneg).comp tendsto_neg_atTop_atBot

/-- The positive remainder's integrated square-root tail vanishes under the original condition. -/
theorem tendsto_positive_remainder_sqrt_tail_zero (μ : Measure ℝ)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞) :
    Tendsto (fun L : ℝ => ∫⁻ t in Ioi (0 : ℝ),
      ((μ.map (fun x : ℝ => max (x - L) 0)) (Ioi t)) ^ (1 / 2 : ℝ))
      atTop (𝓝 0) := by
  simp_rw [positive_remainder_sqrt_tail]
  exact tendsto_martin_positive_tail_zero μ hpos

/-- The negative remainder's integrated square-root tail vanishes under the
closed-tail condition. -/
theorem tendsto_negative_remainder_sqrt_tail_zero (μ : Measure ℝ)
    (hneg : (∫⁻ t in Iio (0 : ℝ), (μ (Iic t)) ^ (1 / 2 : ℝ)) < ∞) :
    Tendsto (fun L : ℝ => ∫⁻ t in Ioi (0 : ℝ),
      ((μ.map (fun x : ℝ => max (-x - L) 0)) (Ioi t)) ^ (1 / 2 : ℝ))
      atTop (𝓝 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_martin_negative_tail_zero μ hneg) (fun _ => zero_le)
    (negative_remainder_sqrt_tail_le μ)

end LPPDifferentiability
