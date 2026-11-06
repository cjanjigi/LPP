/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Probability.CDF
import Mathlib.Tactic.Linarith

/-!
# The pointwise quantile gap for maximum resampling

These are the pointwise facts behind part (ii) of Lemma 4.1 of the
differentiability preprint. The quantile is always the real infimum. The closed
upper tail retains atoms at the quantile. No support or moment assumption is
imposed, and the good-set and conditional-independence arguments are separate.

## References

C. Janjigian, F. Rassoul-Agha and T. Seppäläinen, *Differentiability of the shape
function in the planar corner growth model*, preprint.
-/

public section

open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology

namespace LPPDifferentiability

/-- The quantile set is nonempty at every level below one. -/
theorem source_quantile_set_nonempty (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {y : ℝ} (hy : y < 1) :
    ({s : ℝ | y ≤ μ.real (Iic s)} : Set ℝ).Nonempty := by
  obtain ⟨s, hs⟩ :=
    ((tendsto_cdf_atTop μ).eventually (eventually_gt_nhds hy)).exists
  refine ⟨s, ?_⟩
  change y ≤ μ.real (Iic s)
  rw [← cdf_eq_real]
  exact hs.le

/-- The quantile set is bounded below at every positive level. -/
theorem source_quantile_set_bddBelow (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {y : ℝ} (hy : 0 < y) :
    BddBelow {s : ℝ | y ≤ μ.real (Iic s)} := by
  obtain ⟨a, ha⟩ :=
    ((tendsto_cdf_atBot μ).eventually (eventually_lt_nhds hy)).exists
  refine ⟨a, fun s hs => ?_⟩
  by_contra h
  have hsa : s ≤ a := (lt_of_not_ge h).le
  have hs' : y ≤ cdf μ s := by rwa [cdf_eq_real]
  exact (not_le_of_gt ha) (hs'.trans (monotone_cdf μ hsa))

private theorem exists_right_cdf_lt (μ : Measure ℝ) {t y : ℝ}
    (ht : cdf μ t < y) : ∃ u : ℝ, t < u ∧ cdf μ u < y := by
  have hc := ((cdf μ).right_continuous t).mono Ioi_subset_Ici_self
  have he : ∀ᶠ s in 𝓝[>] t, cdf μ s < y :=
    hc.tendsto.eventually (eventually_lt_nhds ht)
  obtain ⟨u, hu, htu⟩ := (he.and self_mem_nhdsWithin).exists
  exact ⟨u, htu, hu⟩

/-- Right continuity and monotonicity give a strictly positive distance from
`t` to the infimum whenever the level exceeds `F(t)`. -/
theorem lt_source_quantile (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {t y : ℝ} (ht : μ.real (Iic t) < y) (hy : y < 1) :
    t < sInf {s : ℝ | y ≤ μ.real (Iic s)} := by
  have ht' : cdf μ t < y := by rwa [cdf_eq_real]
  obtain ⟨u, htu, hu⟩ := exists_right_cdf_lt μ ht'
  apply htu.trans_le
  apply le_csInf (source_quantile_set_nonempty μ hy)
  intro s hs
  by_contra h
  have hsu : s ≤ u := (lt_of_not_ge h).le
  have hs' : y ≤ cdf μ s := by rwa [cdf_eq_real]
  exact (not_le_of_gt hu) (hs'.trans (monotone_cdf μ hsu))

/-- The closed upper tail of the quantile has mass at least `1-y`.
For points strictly below the infimum, `F(s)<y`; hence `F(q-)≤y`.
The atom at the infimum is included in this upper tail. -/
theorem source_quantile_tail_lower (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {y : ℝ} (hy : 0 < y) :
    1 - y ≤ μ.real (Ici (sInf {s : ℝ | y ≤ μ.real (Iic s)})) := by
  let q : ℝ := sInf {s : ℝ | y ≤ μ.real (Iic s)}
  have hb := source_quantile_set_bddBelow μ hy
  have hbelow : ∀ s < q, cdf μ s < y := by
    intro s hs
    by_contra h
    have hmem : y ≤ μ.real (Iic s) := by
      rw [← cdf_eq_real]
      exact le_of_not_gt h
    exact (not_le_of_gt hs) (csInf_le hb hmem)
  have hleft : Function.leftLim (cdf μ) q ≤ y := by
    apply le_of_tendsto ((monotone_cdf μ).tendsto_leftLim q)
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (hbelow s hs).le
  have hleft_one : Function.leftLim (cdf μ) q ≤ 1 :=
    ((monotone_cdf μ).leftLim_le le_rfl).trans (cdf_le_one μ q)
  have htail : μ.real (Ici q) = 1 - Function.leftLim (cdf μ) q := by
    calc
      μ.real (Ici q) = ((cdf μ).measure (Ici q)).toReal :=
        (congrArg (fun ν : Measure ℝ => (ν (Ici q)).toReal) (measure_cdf μ)).symm
      _ = 1 - Function.leftLim (cdf μ) q := by
        rw [(cdf μ).measure_Ici (tendsto_cdf_atTop μ)]
        exact ENNReal.toReal_ofReal (sub_nonneg.mpr hleft_one)
  change 1 - y ≤ μ.real (Ici q)
  rw [htail]
  exact sub_le_sub_left hleft 1

/-- The shifted level belongs to `(0,1)`, including the endpoint case
`F(t)=1-α`. -/
theorem maximum_quantile_level_mem_Ioo (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {α t : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) (ht : μ.real (Iic t) ≤ 1 - α) :
    μ.real (Iic t) + α / 2 ∈ Ioo (0 : ℝ) 1 := by
  have hnonneg : 0 ≤ μ.real (Iic t) := measureReal_nonneg
  constructor <;> linarith only [hα.1, ht, hnonneg]

/-- The gap `ψ_α(t)` in part (ii) of Lemma 4.1 is strictly positive, with the
exact infimum and no atomlessness or nondegeneracy assumption. -/
theorem maximum_quantile_gap_pos (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {α t : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) (ht : μ.real (Iic t) ≤ 1 - α) :
    0 < sInf {s : ℝ | μ.real (Iic t) + α / 2 ≤ μ.real (Iic s)} - t := by
  apply sub_pos.mpr
  apply lt_source_quantile μ
  · linarith only [hα.1]
  · exact (maximum_quantile_level_mem_Ioo μ hα ht).2

/-- The independent resample's closed upper-tail mass is at least `α/2`.
This is only the pointwise mass estimate, before the Bernoulli trigger and
the finite-field conditional-independence construction. -/
theorem maximum_quantile_tail_lower (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {α t : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) (ht : μ.real (Iic t) ≤ 1 - α) :
    α / 2 ≤ μ.real
      (Ici (sInf {s : ℝ | μ.real (Iic t) + α / 2 ≤ μ.real (Iic s)})) := by
  have hlevel := maximum_quantile_level_mem_Ioo μ hα ht
  calc
    α / 2 ≤ 1 - (μ.real (Iic t) + α / 2) := by linarith only [ht]
    _ ≤ _ := source_quantile_tail_lower μ hlevel.1

end LPPDifferentiability
