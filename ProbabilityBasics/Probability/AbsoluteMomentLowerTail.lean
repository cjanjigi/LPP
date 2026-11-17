/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.AbsoluteMomentTail
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Absolute moments and integrated lower tails

A finite absolute moment above order two gives Martin's integrated square-root condition for the
closed lower tail. Pushing the law forward by absolute value reduces this to the existing positive
tail result, while a strict smaller cutoff preserves atoms at the boundary.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace ProbabilityBasics

/-- Changing variables by `t ↦ -t / 2` turns an integral over negative thresholds into twice the
corresponding integral over positive thresholds. -/
private lemma lintegral_Iio_comp_neg_half (h : ℝ → ℝ≥0∞) (hh : Measurable h) :
    (∫⁻ t in Iio (0 : ℝ), h ((-1 / 2 : ℝ) * t)) =
      ENNReal.ofReal 2 * ∫⁻ t in Ioi (0 : ℝ), h t := by
  let g : ℝ → ℝ := fun t => (-1 / 2 : ℝ) * t
  have hg : Measurable g := by fun_prop
  have hmap : Measure.map g volume = ENNReal.ofReal 2 • volume := by
    change Measure.map (fun t : ℝ => (-1 / 2 : ℝ) * t) volume = _
    rw [Real.map_volume_mul_left (a := (-1 / 2 : ℝ)) (by norm_num : (-1 / 2 : ℝ) ≠ 0)]
    congr 1
    norm_num
  have hindicator : Measurable ((Ioi (0 : ℝ)).indicator h) :=
    hh.indicator measurableSet_Ioi
  have hsign (t : ℝ) : 0 < g t ↔ t < 0 := by
    dsimp [g]
    constructor <;> intro ht <;> nlinarith
  calc
    (∫⁻ t in Iio (0 : ℝ), h (g t)) =
        ∫⁻ t, (Iio (0 : ℝ)).indicator (fun t => h (g t)) t ∂volume := by
          rw [← lintegral_indicator measurableSet_Iio]
    _ = ∫⁻ t, (Ioi (0 : ℝ)).indicator h (g t) ∂volume := by
          apply lintegral_congr
          intro t
          simp only [Set.indicator, mem_Iio, mem_Ioi, hsign]
    _ = ∫⁻ t, (Ioi (0 : ℝ)).indicator h t ∂Measure.map g volume :=
          (lintegral_map hindicator hg).symm
    _ = ENNReal.ofReal 2 * ∫⁻ t in Ioi (0 : ℝ), h t := by
          rw [hmap, lintegral_smul_measure, lintegral_indicator measurableSet_Ioi,
            smul_eq_mul]

/-- A finite absolute moment of order greater than two makes the integrated square root of the
closed lower tail finite. This is Martin (2004), condition (2.7), obtained from Janjigian and
Rassoul-Agha, arXiv:1810.03580v3, assumption (2.1). The closed cutoff includes any atom at the
threshold. -/
theorem integrated_sqrt_lower_tail_lt_top_of_absolute_moment
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {p : ℝ} (hp : 2 < p)
    (hmoment : (∫⁻ x, ENNReal.ofReal (|x| ^ p) ∂μ) < ∞) :
    (∫⁻ t in Iio (0 : ℝ), (μ (Iic t)) ^ (1 / 2 : ℝ)) < ∞ := by
  have hp0 : 0 < p := by linarith only [hp]
  let ν : Measure ℝ := μ.map abs
  have hνprob : IsProbabilityMeasure ν := by
    dsimp [ν]
    exact (Measure.isProbabilityMeasure_map_iff continuous_abs.measurable.aemeasurable).2 inferInstance
  have habsMomentMeas : Measurable (fun y : ℝ => ENNReal.ofReal (|y| ^ p)) := by
    have hpow : Measurable (fun y : ℝ => |y| ^ p) :=
      ((Real.continuous_rpow_const hp0.le).comp continuous_abs).measurable
    exact ENNReal.measurable_ofReal.comp hpow
  have hνmomentEq :
      (∫⁻ y, ENNReal.ofReal (|y| ^ p) ∂ν) =
        ∫⁻ x, ENNReal.ofReal (|x| ^ p) ∂μ := by
    change (∫⁻ y, ENNReal.ofReal (|y| ^ p) ∂Measure.map abs μ) = _
    rw [lintegral_map habsMomentMeas continuous_abs.measurable]
    apply lintegral_congr
    intro x
    simp only [abs_abs]
  have hνmoment : (∫⁻ y, ENNReal.ofReal (|y| ^ p) ∂ν) < ∞ := by
    rw [hνmomentEq]
    exact hmoment
  obtain ⟨_, hpositiveTail⟩ :=
    @negative_moment_and_positive_tail_of_absolute_moment ν hνprob p hp hνmoment
  let h : ℝ → ℝ≥0∞ := fun u => (ν (Ioi u)) ^ (1 / 2 : ℝ)
  have hmeasureAnti : Antitone (fun u : ℝ => ν (Ioi u)) := by
    intro a b hab
    exact measure_mono (Ioi_subset_Ioi hab)
  have hmeas : Measurable h := by
    change Measurable (fun u : ℝ => (ν (Ioi u)) ^ (1 / 2 : ℝ))
    exact ENNReal.continuous_rpow_const.measurable.comp hmeasureAnti.measurable
  let g : ℝ → ℝ := fun t => (-1 / 2 : ℝ) * t
  have htail (t : ℝ) (ht : t < 0) : μ (Iic t) ≤ ν (Ioi (g t)) := by
    change μ (Iic t) ≤ (μ.map abs) (Ioi (g t))
    rw [Measure.map_apply continuous_abs.measurable measurableSet_Ioi]
    apply measure_mono
    intro x hx
    change x ≤ t at hx
    have hx0 : x ≤ 0 := hx.trans ht.le
    simp only [Set.mem_preimage, mem_Ioi]
    rw [abs_of_nonpos hx0]
    dsimp [g]
    linarith only [hx, ht]
  have htailSqrt (t : ℝ) (ht : t < 0) :
      (μ (Iic t)) ^ (1 / 2 : ℝ) ≤ h (g t) := by
    exact ENNReal.rpow_le_rpow (htail t ht) (by norm_num)
  have hcomparison : (∫⁻ t in Iio (0 : ℝ), h (g t)) < ∞ := by
    rw [lintegral_Iio_comp_neg_half h hmeas]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hpositiveTail
  calc
    (∫⁻ t in Iio (0 : ℝ), (μ (Iic t)) ^ (1 / 2 : ℝ)) ≤
        ∫⁻ t in Iio (0 : ℝ), h (g t) :=
      setLIntegral_mono' measurableSet_Iio fun t ht => htailSqrt t ht
    _ < ∞ := hcomparison

end ProbabilityBasics
