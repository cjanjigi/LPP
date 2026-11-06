/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Probability.PassageIntegrable
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# First moments under Martin's two square-root tail conditions

The hypotheses here are the two square-root tail conditions (2.6) and (2.7) of Martin (2004).
The proof uses layer cake for the positive and negative parts. The closed negative
tail in the hypothesis bounds the strict negative tail without removing atoms.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace LPPDifferentiability

private theorem measure_le_sqrt (μ : Measure ℝ) [IsProbabilityMeasure μ] (s : Set ℝ) :
    μ s ≤ (μ s) ^ (1 / 2 : ℝ) := by
  calc
    μ s = (μ s) ^ (1 : ℝ) := (ENNReal.rpow_one _).symm
    _ ≤ (μ s) ^ (1 / 2 : ℝ) :=
      ENNReal.rpow_le_rpow_of_exponent_ge (prob_le_one) (by norm_num)

private theorem integrable_max_zero_of_tail (μ : Measure ℝ) (f : ℝ → ℝ)
    (hf : Measurable f)
    (htail : (∫⁻ t in Ioi (0 : ℝ), μ {x | t < f x}) < ∞) :
    Integrable (fun x => max (f x) 0) μ := by
  refine ⟨(hf.max measurable_const).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (f := fun x => max (f x) 0)
    (Filter.Eventually.of_forall fun x => le_max_right (f x) 0)]
  rw [lintegral_eq_lintegral_meas_lt μ
    (Filter.Eventually.of_forall fun x => le_max_right (f x) 0)
    (hf.max measurable_const).aemeasurable]
  convert htail using 1
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  congr 1
  ext x
  simp only [mem_ofPred_eq, lt_max_iff, not_lt.mpr (le_of_lt ht), or_false]

/-- Martin's two integrated square-root tails imply an integrable marginal weight. -/
theorem integrable_id_of_martin_tails (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : (∫⁻ t in Iio (0 : ℝ), (μ (Iic t)) ^ (1 / 2 : ℝ)) < ∞)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞) :
    Integrable (fun x : ℝ => x) μ := by
  have hp : Integrable (fun x : ℝ => max x 0) μ := by
    apply integrable_max_zero_of_tail μ _ measurable_id
    exact lt_of_le_of_lt (lintegral_mono fun t => measure_le_sqrt μ (Ioi t)) hpos
  have hchange :
      (∫⁻ t in Ioi (0 : ℝ), (μ (Iic (-t))) ^ (1 / 2 : ℝ)) =
      ∫⁻ t in Iio (0 : ℝ), (μ (Iic t)) ^ (1 / 2 : ℝ) := by
    have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).setLIntegral_comp_preimage_emb
      (MeasurableEquiv.neg ℝ).measurableEmbedding
      (fun t : ℝ => (μ (Iic t)) ^ (1 / 2 : ℝ)) (Iio 0)
    have hpre : (fun t : ℝ => -t) ⁻¹' Iio (0 : ℝ) = Ioi 0 := by
      ext t
      simp only [mem_preimage, mem_Iio, mem_Ioi, neg_lt_zero]
    rw [hpre] at h
    exact h
  have hn : Integrable (fun x : ℝ => max (-x) 0) μ := by
    apply integrable_max_zero_of_tail μ _ measurable_id.neg
    have hbound : (∫⁻ t in Ioi (0 : ℝ), (μ (Iic (-t))) ^ (1 / 2 : ℝ)) < ∞ := by
      rw [hchange]
      exact hneg
    apply lt_of_le_of_lt _ hbound
    apply lintegral_mono
    intro t
    exact le_trans (measure_mono (by intro x hx; change t < -x at hx; change x ≤ -t; linarith only [hx]))
      (measure_le_sqrt μ (Iic (-t)))
  convert hp.sub hn using 1
  ext x
  dsimp
  rcases le_total 0 x with hx | hx
  · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx), sub_zero]
  · rw [max_eq_right hx, max_eq_left (neg_nonneg.mpr hx), zero_sub, neg_neg]

/-- Each terminal-excluded path sum is integrable under Martin's tails. -/
theorem integrable_pathWeight_of_martin_tails (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : (∫⁻ t in Iio (0 : ℝ), (μ (Iic t)) ^ (1 / 2 : ℝ)) < ∞)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞)
    {u : Lattice} {d : ℕ × ℕ} (p : Path u d) :
    Integrable (fun ω : Environment => pathWeight ω p) (environmentLaw μ) :=
  integrable_pathWeight μ (integrable_id_of_martin_tails μ hneg hpos) p

/-- The finite last-passage maximum is integrable under Martin's tails. -/
theorem integrable_lastPassage_of_martin_tails (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : (∫⁻ t in Iio (0 : ℝ), (μ (Iic t)) ^ (1 / 2 : ℝ)) < ∞)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞)
    (u : Lattice) (d : ℕ × ℕ) :
    Integrable (fun ω : Environment => lastPassage ω u d) (environmentLaw μ) :=
  integrable_lastPassage μ (integrable_id_of_martin_tails μ hneg hpos) u d

end LPPDifferentiability
