/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.MaximumQuantileGap
import Martin2004.Probability.MaximumQuantileMeasurability
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.Tactic.Linarith

/-!
# Good sets for maximum resampling

The two decreasing-set steps of part (ii) of Lemma 4.1 of the differentiability
preprint, restricted to the domain `{t | μ.real (Iic t) < 1}`. This domain is
not a definition of the top support endpoint. The real infimum preserves atoms.

## References

C. Janjigian, F. Rassoul-Agha and T. Seppäläinen, *Differentiability of the shape
function in the planar corner growth model*, preprint.
-/

public section

open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology

namespace LPPDifferentiability

private theorem real_measure_tendsto_zero_of_antitone_empty
    (μ : Measure ℝ) [IsFiniteMeasure μ] (A : ℕ → Set ℝ)
    (hA : ∀ n, MeasurableSet (A n)) (hmono : Antitone A)
    (hempty : ⋂ n, A n = ∅) :
    Tendsto (fun n => μ.real (A n)) atTop (𝓝 0) := by
  have hlim := tendsto_measure_iInter_atTop
    (fun n => (hA n).nullMeasurableSet) hmono ⟨0, measure_ne_top μ _⟩
  rw [hempty, measure_empty] at hlim
  exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim

/-- The first decreasing-set step in part (ii) of Lemma 4.1: choose a small
positive CDF cutoff whose exceptional mass on `F<1` is arbitrarily small. -/
theorem maximum_cdf_cutoff_small_exception (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {β : ℝ} (hβ : 0 < β) :
    ∃ α ∈ Ioo (0 : ℝ) (1 / 2),
      μ.real {t : ℝ | μ.real (Iic t) < 1 ∧ 1 - α < μ.real (Iic t)} ≤ β := by
  let a : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 3)
  let A : ℕ → Set ℝ := fun n =>
    {t : ℝ | μ.real (Iic t) < 1 ∧ 1 - a n < μ.real (Iic t)}
  have ha_pos (n : ℕ) : 0 < a n := by
    dsimp only [a]
    positivity
  have ha_small (n : ℕ) : a n < 1 / 2 := by
    dsimp only [a]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    apply (div_lt_div_iff₀ (by positivity : (0 : ℝ) < n + 3)
      (by norm_num : (0 : ℝ) < 2)).2
    linarith only [hn]
  have ha_mono : Antitone a := by
    intro n m hnm
    dsimp only [a]
    exact one_div_le_one_div_of_le (by positivity)
      (add_le_add (Nat.cast_le.mpr hnm) le_rfl)
  have ha_zero : Tendsto a atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat 2)
    norm_num only [Function.comp_def, Nat.cast_add, Nat.cast_ofNat, add_assoc] at h
    exact h
  have hF : Measurable (fun t : ℝ => μ.real (Iic t)) := by
    have heq : (fun t : ℝ => μ.real (Iic t)) = fun t => cdf μ t := by
      funext t
      exact (cdf_eq_real μ t).symm
    rw [heq]
    exact (monotone_cdf μ).measurable
  have hA (n : ℕ) : MeasurableSet (A n) :=
    (measurableSet_lt hF measurable_const).inter
      (measurableSet_lt measurable_const hF)
  have hmono : Antitone A := by
    intro n m hnm t ht
    exact ⟨ht.1, (sub_le_sub_left (ha_mono hnm) 1).trans_lt ht.2⟩
  have hempty : ⋂ n, A n = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro t ht
    have htall := mem_iInter.mp ht
    have htone : μ.real (Iic t) < 1 := (htall 0).1
    obtain ⟨n, hn⟩ := (ha_zero.eventually
      (eventually_lt_nhds (sub_pos.mpr htone))).exists
    have hnA := (htall n).2
    linarith only [hn, hnA]
  have hlim := real_measure_tendsto_zero_of_antitone_empty μ A hA hmono hempty
  obtain ⟨n, hn⟩ := (hlim.eventually (eventually_lt_nhds hβ)).exists
  exact ⟨a n, ⟨ha_pos n, ha_small n⟩, hn.le⟩

/-- The second decreasing-set step, after fixing the first cutoff. -/
theorem maximum_quantile_gap_small_exception (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {α β : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) (hβ : 0 < β) :
    ∃ c > 0, μ.real {t : ℝ | μ.real (Iic t) ≤ 1 - α ∧
      sInf {s : ℝ | μ.real (Iic t) + α / 2 ≤ μ.real (Iic s)} - t < c} ≤ β := by
  let c : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let B : ℕ → Set ℝ := fun n => {t : ℝ | μ.real (Iic t) ≤ 1 - α ∧
    sInf {s : ℝ | μ.real (Iic t) + α / 2 ≤ μ.real (Iic s)} - t < c n}
  have hc_pos (n : ℕ) : 0 < c n := by
    dsimp only [c]
    positivity
  have hc_mono : Antitone c := by
    intro n m hnm
    dsimp only [c]
    exact one_div_le_one_div_of_le (by positivity)
      (add_le_add (Nat.cast_le.mpr hnm) le_rfl)
  have hc_zero : Tendsto c atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hB (n : ℕ) : MeasurableSet (B n) :=
    maximum_quantile_gap_sublevel_measurableSet μ hα (c n)
  have hmono : Antitone B := by
    intro n m hnm t ht
    exact ⟨ht.1, ht.2.trans_le (hc_mono hnm)⟩
  have hempty : ⋂ n, B n = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro t ht
    have htall := mem_iInter.mp ht
    have hgap := maximum_quantile_gap_pos μ hα (htall 0).1
    obtain ⟨n, hn⟩ := (hc_zero.eventually (eventually_lt_nhds hgap)).exists
    exact (not_lt_of_ge (htall n).2.le) hn
  have hlim := real_measure_tendsto_zero_of_antitone_empty μ B hB hmono hempty
  obtain ⟨n, hn⟩ := (hlim.eventually (eventually_lt_nhds hβ)).exists
  exact ⟨c n, hc_pos n, hn.le⟩

/-- The near-full good set on the domain `F<1`. -/
theorem maximum_quantile_internal_good_set (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {β : ℝ} (hβ : 0 < β) :
    ∃ α ∈ Ioo (0 : ℝ) (1 / 2), ∃ c > 0,
      μ.real {t : ℝ | μ.real (Iic t) < 1 ∧
        ¬(μ.real (Iic t) ≤ 1 - α ∧
          c ≤ sInf {s : ℝ | μ.real (Iic t) + α / 2 ≤ μ.real (Iic s)} - t)} ≤ β := by
  obtain ⟨α, hα, hA⟩ := maximum_cdf_cutoff_small_exception μ (half_pos hβ)
  have hαone : α ∈ Ioo (0 : ℝ) 1 :=
    ⟨hα.1, hα.2.trans (by norm_num)⟩
  obtain ⟨c, hc, hB⟩ := maximum_quantile_gap_small_exception μ hαone (half_pos hβ)
  refine ⟨α, hα, c, hc, ?_⟩
  let A : Set ℝ := {t : ℝ | μ.real (Iic t) < 1 ∧ 1 - α < μ.real (Iic t)}
  let B : Set ℝ := {t : ℝ | μ.real (Iic t) ≤ 1 - α ∧
    sInf {s : ℝ | μ.real (Iic t) + α / 2 ≤ μ.real (Iic s)} - t < c}
  calc
    _ ≤ μ.real (A ∪ B) := by
      apply measureReal_mono (μ := μ) ?_ (measure_ne_top μ _)
      intro t ht
      by_cases hdom : μ.real (Iic t) ≤ 1 - α
      · exact Or.inr ⟨hdom, lt_of_not_ge (fun hgap => ht.2 ⟨hdom, hgap⟩)⟩
      · exact Or.inl ⟨ht.1, lt_of_not_ge hdom⟩
    _ ≤ μ.real A + μ.real B := measureReal_union_le _ _
    _ ≤ β / 2 + β / 2 := add_le_add hA hB
    _ = β := add_halves β

end LPPDifferentiability
