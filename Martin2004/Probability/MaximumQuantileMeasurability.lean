/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.MaximumQuantileGap

/-!
# Measurable sets for the maximum-resampling quantile gap

Part (ii) of Lemma 4.1 of the differentiability preprint uses continuity from
above for gap sublevel sets. These lemmas supply the omitted measurability
detail. The inverse is always the real infimum, evaluated only at levels in
`(0,1)`. No quantile value outside that interval is introduced.

## References

C. Janjigian, F. Rassoul-Agha and T. Seppäläinen, *Differentiability of the shape
function in the planar corner growth model*, preprint.
-/

public section

open MeasureTheory Set ProbabilityTheory

namespace LPPDifferentiability

/-- The quantile infimum is monotone on its level domain. -/
theorem source_quantile_monotone (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Monotone (fun y : Ioo (0 : ℝ) 1 => sInf {s : ℝ | y.1 ≤ μ.real (Iic s)}) := by
  intro y z hyz
  have hyz' : y.1 ≤ z.1 := hyz
  apply le_csInf (source_quantile_set_nonempty μ z.property.2)
  intro s hs
  exact csInf_le (source_quantile_set_bddBelow μ y.property.1) (hyz'.trans hs)

/-- Monotonicity makes the inverse Borel measurable on `(0,1)`. -/
theorem source_quantile_measurable (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Measurable (fun y : Ioo (0 : ℝ) 1 => sInf {s : ℝ | y.1 ≤ μ.real (Iic s)}) :=
  (source_quantile_monotone μ).measurable

/-- The distribution function `t ↦ μ.real (Iic t)` of a probability measure on `ℝ` is Borel
measurable. -/
theorem measurable_measureReal_Iic (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Measurable (fun t : ℝ => μ.real (Iic t)) := by
  have heq : (fun t : ℝ => μ.real (Iic t)) = (fun t : ℝ => cdf μ t) := by
    funext t
    exact (cdf_eq_real μ t).symm
  rw [heq]
  exact (monotone_cdf μ).measurable

/-- The quantile gap is measurable on the domain `F(t)≤1-α`, including its
equality case. -/
theorem maximum_quantile_gap_measurable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    Measurable (fun t : {t : ℝ // μ.real (Iic t) ≤ 1 - α} =>
      sInf {s : ℝ | μ.real (Iic t.1) + α / 2 ≤ μ.real (Iic s)} - t.1) := by
  have hshift : Measurable (fun t : {t : ℝ // μ.real (Iic t) ≤ 1 - α} =>
      (⟨μ.real (Iic t.1) + α / 2,
        maximum_quantile_level_mem_Ioo μ hα t.property⟩ : Ioo (0 : ℝ) 1)) :=
    (((measurable_measureReal_Iic μ).comp measurable_subtype_coe).add_const (α / 2)).subtype_mk
  exact ((source_quantile_measurable μ).comp hshift).sub measurable_subtype_coe

/-- The exact real sublevel set used in the decreasing-set argument is
measurable. No value of the inverse outside its domain is needed. -/
theorem maximum_quantile_gap_sublevel_measurableSet (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) (c : ℝ) :
    MeasurableSet {t : ℝ | μ.real (Iic t) ≤ 1 - α ∧
      sInf {s : ℝ | μ.real (Iic t) + α / 2 ≤ μ.real (Iic s)} - t < c} := by
  let D := {t : ℝ | μ.real (Iic t) ≤ 1 - α}
  have hD : MeasurableSet D := measurableSet_le (measurable_measureReal_Iic μ) measurable_const
  have hsub : MeasurableSet {t : D |
      sInf {s : ℝ | μ.real (Iic t.1) + α / 2 ≤ μ.real (Iic s)} - t.1 < c} :=
    measurableSet_lt (maximum_quantile_gap_measurable μ hα) measurable_const
  have hset : ((↑) : D → ℝ) '' {t : D |
      sInf {s : ℝ | μ.real (Iic t.1) + α / 2 ≤ μ.real (Iic s)} - t.1 < c} =
      {t : ℝ | μ.real (Iic t) ≤ 1 - α ∧
        sInf {s : ℝ | μ.real (Iic t) + α / 2 ≤ μ.real (Iic s)} - t < c} := by
    ext t
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u.property, hu⟩
    · rintro ⟨ht, hgap⟩
      exact ⟨⟨t, ht⟩, hgap, rfl⟩
  rw [← hset]
  exact hD.subtype_image hsub

/-- The exact real superlevel set defining the good quantile-gap region is
measurable, with the atom and equality cases unchanged. -/
theorem maximum_quantile_gap_superlevel_measurableSet (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) (c : ℝ) :
    MeasurableSet {t : ℝ | μ.real (Iic t) ≤ 1 - α ∧
      c ≤ sInf {s : ℝ | μ.real (Iic t) + α / 2 ≤ μ.real (Iic s)} - t} := by
  let D := {t : ℝ | μ.real (Iic t) ≤ 1 - α}
  have hD : MeasurableSet D := measurableSet_le (measurable_measureReal_Iic μ) measurable_const
  have hsuper : MeasurableSet {t : D |
      c ≤ sInf {s : ℝ | μ.real (Iic t.1) + α / 2 ≤ μ.real (Iic s)} - t.1} :=
    measurableSet_le measurable_const (maximum_quantile_gap_measurable μ hα)
  have hset : ((↑) : D → ℝ) '' {t : D |
      c ≤ sInf {s : ℝ | μ.real (Iic t.1) + α / 2 ≤ μ.real (Iic s)} - t.1} =
      {t : ℝ | μ.real (Iic t) ≤ 1 - α ∧
        c ≤ sInf {s : ℝ | μ.real (Iic t) + α / 2 ≤ μ.real (Iic s)} - t} := by
    ext t
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u.property, hu⟩
    · rintro ⟨ht, hgap⟩
      exact ⟨⟨t, ht⟩, hgap, rfl⟩
  rw [← hset]
  exact hD.subtype_image hsuper

end LPPDifferentiability
