/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.MaximumConditionalBoost
public import ProbabilityBasics.Probability.SupportTopCDF
import Differentiability.Probability.MaximumQuantileGoodSet
import Martin2004.Probability.MaximumQuantileMeasurability
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# The complete good set for maximum resampling

The good set consists of points below the EReal supremum of the measure support
that satisfy the CDF cutoff and quantile-gap bound. Its union with the possible
top atom has complement mass at most the requested beta. The fixed-environment
boost and independence conclusions use the same quantile witnesses.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LPPDifferentiability

/-- The good set, its near-full mass bound, and the fixed-environment
maximum-resampling boost and independence conclusions, with one shared pair
of witnesses chosen before the resampling parameters and the environment. -/
theorem maximum_kernel_good_set (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {β : ℝ} (hβ : 0 < β) :
    let M : EReal := sSup ((fun s : ℝ => (s : EReal)) '' μ.support)
    ∃ α ∈ Ioo (0 : ℝ) (1 / 2), ∃ c > 0,
      let I : Set ℝ := {t : ℝ | (t : EReal) < M ∧
        μ.real (Iic t) ≤ 1 - α ∧
        c ≤ sInf {s : ℝ | μ.real (Iic t) + α / 2 ≤ μ.real (Iic s)} - t}
      MeasurableSet I ∧
      μ.real ((I ∪ {t : ℝ | (t : EReal) = M})ᶜ) ≤ β ∧
      ∀ δ : ℝ, δ ∈ Icc (0 : ℝ) 1 →
        ∀ w : Environment, ∀ R : Finset Lattice,
          (∀ v : Lattice, v ∈ R → w v ∈ I →
            δ * α / 2 ≤
              ((environmentLaw μ).prod (Measure.infinitePi (fun _ : Lattice =>
                ENNReal.ofReal (1 - δ) • Measure.dirac false +
                  ENNReal.ofReal δ • Measure.dirac true))).real
                {p : Environment × (Lattice → Bool) |
                  w v + c ≤ if v ∈ R ∧ p.2 v = true then
                    max (w v) (p.1 v) else w v}) ∧
          iIndepFun (fun v (p : Environment × (Lattice → Bool)) =>
            if w v + c ≤
              (if v ∈ R ∧ p.2 v = true then max (w v) (p.1 v) else w v)
            then (1 : ℝ) else 0)
            ((environmentLaw μ).prod (Measure.infinitePi (fun _ : Lattice =>
              ENNReal.ofReal (1 - δ) • Measure.dirac false +
                ENNReal.ofReal δ • Measure.dirac true))) := by
  dsimp only
  obtain ⟨α, hα, c, hc, hbad⟩ := maximum_quantile_internal_good_set μ hβ
  let M : EReal := sSup ((fun s : ℝ => (s : EReal)) '' μ.support)
  let I : Set ℝ := {t : ℝ | (t : EReal) < M ∧
    μ.real (Iic t) ≤ 1 - α ∧
    c ≤ sInf {s : ℝ | μ.real (Iic t) + α / 2 ≤ μ.real (Iic s)} - t}
  let below : Set ℝ := {t : ℝ | (t : EReal) < M}
  let top : Set ℝ := {t : ℝ | (t : EReal) = M}
  let bad : Set ℝ := {t : ℝ | μ.real (Iic t) < 1 ∧
    ¬(μ.real (Iic t) ≤ 1 - α ∧
      c ≤ sInf {s : ℝ | μ.real (Iic t) + α / 2 ≤ μ.real (Iic s)} - t)}
  have hα01 : α ∈ Ioo (0 : ℝ) 1 := by
    exact ⟨hα.1, hα.2.trans (by norm_num)⟩
  have hbad_bound : μ.real bad ≤ β := by
    simpa only [bad] using hbad
  have hcoemeas : Measurable (fun t : ℝ => (t : EReal)) :=
    continuous_coe_real_ereal.measurable
  have hbelow_meas : MeasurableSet below := by
    change MeasurableSet {t : ℝ | (t : EReal) < M}
    exact measurableSet_lt hcoemeas measurable_const
  have hgood_meas : MeasurableSet {t : ℝ |
      μ.real (Iic t) ≤ 1 - α ∧
        c ≤ sInf {s : ℝ | μ.real (Iic t) + α / 2 ≤ μ.real (Iic s)} - t} :=
    maximum_quantile_gap_superlevel_measurableSet μ hα01 c
  have hI_meas : MeasurableSet I := by
    change MeasurableSet (below ∩ {t : ℝ |
      μ.real (Iic t) ≤ 1 - α ∧
        c ≤ sInf {s : ℝ | μ.real (Iic t) + α / 2 ≤ μ.real (Iic s)} - t})
    exact hbelow_meas.inter hgood_meas
  have hpartition : μ ((below ∪ top)ᶜ) = 0 := by
    simpa only [below, top, M] using
      (source_measure_compl_below_or_top_eq_zero μ)
  have hcdf_below (t : ℝ) : μ.real (Iic t) < 1 ↔ t ∈ below := by
    simpa only [below, M, Set.mem_ofPred_eq] using
      (source_cdf_lt_one_iff_lt_support_sSup μ t)
  have hmass : μ.real ((I ∪ top)ᶜ) ≤ β := by
    have hsubset : (I ∪ top)ᶜ ⊆ bad ∪ (below ∪ top)ᶜ := by
      intro t ht
      have hnotI : t ∉ I := fun hi => ht (Or.inl hi)
      have hnottop : t ∉ top := fun hi => ht (Or.inr hi)
      by_cases hpartition_mem : t ∈ below ∪ top
      · rcases hpartition_mem with hbelow | htop
        · left
          refine ⟨(hcdf_below t).2 hbelow, ?_⟩
          intro hgood
          apply hnotI
          exact ⟨hbelow, hgood.1, hgood.2⟩
        · exact False.elim (hnottop htop)
      · exact Or.inr hpartition_mem
    have hpartition_real : μ.real ((below ∪ top)ᶜ) = 0 := by
      rw [measureReal_def, hpartition, ENNReal.toReal_zero]
    calc
      μ.real ((I ∪ top)ᶜ) ≤ μ.real (bad ∪ (below ∪ top)ᶜ) :=
        measureReal_mono (μ := μ) hsubset (measure_ne_top μ _)
      _ ≤ μ.real bad + μ.real ((below ∪ top)ᶜ) := measureReal_union_le _ _
      _ = μ.real bad := by rw [hpartition_real, add_zero]
      _ ≤ β := hbad_bound
  refine ⟨α, hα, c, hc, ?_⟩
  refine ⟨hI_meas, hmass, ?_⟩
  intro δ hδ w R
  constructor
  · intro v hv hgood
    change (w v : EReal) < M ∧
      μ.real (Iic (w v)) ≤ 1 - α ∧
        c ≤ sInf {s : ℝ | μ.real (Iic (w v)) + α / 2 ≤ μ.real (Iic s)} - w v
      at hgood
    exact maximum_resampling_fiber_boost_probability_lower μ hδ hα01 hc
      w R v hv hgood.2.1 hgood.2.2
  · exact iIndepFun_maximum_resampling_fiber_boost μ hδ w R c

end LPPDifferentiability
