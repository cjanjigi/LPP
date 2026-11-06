/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Vanishing tails of finite nonnegative integrals

Dominated convergence applies to the indicators of shrinking half-lines.
Only finiteness on the appropriate original half-line is needed.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace LPPDifferentiability

/-- A finite upper-tail integral has vanishing tails at positive infinity. -/
theorem tendsto_lintegral_Ioi_zero_of_lt_top (f : ℝ → ℝ≥0∞)
    (hf : Measurable f) (a : ℝ)
    (hfin : (∫⁻ t in Ioi a, f t) < ∞) :
    Tendsto (fun L : ℝ => ∫⁻ t in Ioi L, f t) atTop (𝓝 0) := by
  have h := tendsto_lintegral_filter_of_dominated_convergence
    (l := atTop) (μ := volume.restrict (Ioi a)) (F := fun L : ℝ => (Ioi L).indicator f)
    (f := fun _ => 0) f
    (Eventually.of_forall fun L => hf.indicator measurableSet_Ioi)
    (Eventually.of_forall fun L => Eventually.of_forall fun t => (indicator_le_self _ _) t)
    hfin.ne ?_
  · simp only [lintegral_zero] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop a] with L hL
    rw [lintegral_indicator measurableSet_Ioi,
      Measure.restrict_restrict_of_subset (Ioi_subset_Ioi hL)]
  · exact Eventually.of_forall fun t => tendsto_const_nhds.congr' (by
      filter_upwards [eventually_ge_atTop t] with L hL
      exact (indicator_of_notMem (show t ∉ Ioi L from not_lt.mpr hL) f).symm)

/-- A finite lower-tail integral has vanishing tails at negative infinity. -/
theorem tendsto_lintegral_Iio_zero_of_lt_top (f : ℝ → ℝ≥0∞)
    (hf : Measurable f) (a : ℝ)
    (hfin : (∫⁻ t in Iio a, f t) < ∞) :
    Tendsto (fun L : ℝ => ∫⁻ t in Iio L, f t) atBot (𝓝 0) := by
  have h := tendsto_lintegral_filter_of_dominated_convergence
    (l := atBot) (μ := volume.restrict (Iio a)) (F := fun L : ℝ => (Iio L).indicator f)
    (f := fun _ => 0) f
    (Eventually.of_forall fun L => hf.indicator measurableSet_Iio)
    (Eventually.of_forall fun L => Eventually.of_forall fun t => (indicator_le_self _ _) t)
    hfin.ne ?_
  · simp only [lintegral_zero] at h
    apply h.congr'
    filter_upwards [eventually_le_atBot a] with L hL
    rw [lintegral_indicator measurableSet_Iio,
      Measure.restrict_restrict_of_subset (Iio_subset_Iio hL)]
  · exact Eventually.of_forall fun t => tendsto_const_nhds.congr' (by
      filter_upwards [eventually_le_atBot t] with L hL
      exact (indicator_of_notMem (show t ∉ Iio L from not_lt.mpr hL) f).symm)

end LPPDifferentiability
