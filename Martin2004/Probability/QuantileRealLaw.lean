/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.InverseCDFLaw
public import Mathlib.MeasureTheory.Constructions.Pi

/-! # The literal quantile under real restricted uniform volume -/

public section

open MeasureTheory Set

namespace LPPDifferentiability

/-- The literal formula is almost everywhere measurable for real uniform input. -/
theorem aemeasurable_source_quantile_real (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    AEMeasurable (fun y : ℝ => sInf {r : ℝ | y ≤ μ.real (Iic r)})
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
  exact aemeasurable_restrict_of_measurable_subtype measurableSet_Ioo
    (measurable_source_quantile μ)

/-- Transfer the quantile law from the open-interval subtype to real uniform input,
retaining the specified endpoint values. -/
theorem map_source_quantile_real (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (volume.restrict (Ioo (0 : ℝ) 1)).map
      (fun y : ℝ => sInf {r : ℝ | y ≤ μ.real (Iic r)}) = μ := by
  rw [← map_comap_subtype_coe measurableSet_Ioo]
  rw [(show AEMeasurable (fun y : ℝ => sInf {r : ℝ | y ≤ μ.real (Iic r)})
    ((Measure.comap (Subtype.val : Ioo (0 : ℝ) 1 → ℝ) volume).map Subtype.val) by
      rw [map_comap_subtype_coe measurableSet_Ioo]
      exact aemeasurable_source_quantile_real μ).map_map_of_aemeasurable
        measurable_subtype_coe.aemeasurable]
  exact map_source_quantile μ

/-- Coordinatewise literal quantiles carry finite uniform products to product mu.
The finite index type may be empty. -/
theorem map_source_quantile_real_pi (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {ι : Type*} [Fintype ι] :
    (Measure.pi (fun _ : ι => volume.restrict (Ioo (0 : ℝ) 1))).map
      (fun u : ι → ℝ => fun i => sInf {r : ℝ | u i ≤ μ.real (Iic r)}) =
        Measure.pi (fun _ : ι => μ) := by
  have : IsProbabilityMeasure ((volume.restrict (Ioo (0 : ℝ) 1)).map
      (fun y : ℝ => sInf {r : ℝ | y ≤ μ.real (Iic r)})) := by
    rw [map_source_quantile_real μ]
    infer_instance
  rw [Measure.pi_map_pi (fun _ : ι => aemeasurable_source_quantile_real μ)]
  simp_rw [map_source_quantile_real μ]

end LPPDifferentiability
