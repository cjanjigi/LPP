/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.InverseCDF
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The law of the literal quantile on the open unit interval

Lebesgue measure is pulled back along the actual subtype embedding. Its mass
and the quantile pushforward are proved here, with no supplied law identity.
-/

public section

open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology

namespace LPPDifferentiability

/-- The genuine open unit interval with comapped Lebesgue measure has mass one. -/
theorem open_unit_comap_probability :
    IsProbabilityMeasure (Measure.comap
      (Subtype.val : {u : ℝ // u ∈ Ioo (0 : ℝ) 1} → ℝ) volume) := by
  constructor
  rw [comap_subtype_coe_apply measurableSet_Ioo, image_univ, Subtype.range_coe,
    Real.volume_Ioo]
  norm_num

/-- The exact half-line preimage, before taking its Lebesgue measure. -/
theorem source_quantile_Iic_image (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    (Subtype.val : {u : ℝ // u ∈ Ioo (0 : ℝ) 1} → ℝ) ''
      ((fun u : {u : ℝ // u ∈ Ioo (0 : ℝ) 1} => sInf {s : ℝ | (u : ℝ) ≤ μ.real (Iic s)}) ⁻¹' Iic t) =
      Ioo (0 : ℝ) 1 ∩ Iic (μ.real (Iic t)) := by
  ext u
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v.property, (source_quantile_le_iff μ v.property).1 hv⟩
  · rintro ⟨hu, ht⟩
    exact ⟨⟨u, hu⟩, (source_quantile_le_iff μ hu).2 ht, rfl⟩

private theorem volume_open_unit_inter_Iic {a : ℝ} (ha : a ≤ 1) :
    volume (Ioo (0 : ℝ) 1 ∩ Iic a) = ENNReal.ofReal a := by
  calc
    volume (Ioo (0 : ℝ) 1 ∩ Iic a) = volume (Ioc (0 : ℝ) 1 ∩ Iic a) := by
      apply measure_congr
      filter_upwards [Ioo_ae_eq_Ioc (μ := (volume : Measure ℝ)) (a := (0 : ℝ)) (b := 1)]
        with x hx
      simp only [mem_inter_iff]
      exact congrArg (fun p : Prop => p ∧ x ∈ Iic a) hx
    _ = ENNReal.ofReal a := by
      rw [Ioc_inter_Iic, inf_eq_right.mpr ha, Real.volume_Ioc, sub_zero]

/-- Uniform input on the genuine open unit interval produces the original law.
The quantile is exactly the real infimum from the manuscript. -/
theorem map_source_quantile (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (Measure.comap (Subtype.val : {u : ℝ // u ∈ Ioo (0 : ℝ) 1} → ℝ) volume).map
      (fun u : {u : ℝ // u ∈ Ioo (0 : ℝ) 1} => sInf {s : ℝ | (u : ℝ) ≤ μ.real (Iic s)}) = μ := by
  have := open_unit_comap_probability
  apply Measure.ext_of_Iic
  intro t
  rw [Measure.map_apply (measurable_source_quantile μ) measurableSet_Iic,
    comap_subtype_coe_apply measurableSet_Ioo, source_quantile_Iic_image]
  rw [volume_open_unit_inter_Iic]
  · rw [← cdf_eq_real]
    exact ofReal_cdf μ t
  · rw [← cdf_eq_real]
    exact cdf_le_one μ t

end LPPDifferentiability
