/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.FinalDraft.CrossingRemarks.Translation

import Differentiability.Model.LevelIntervalAttachments
import LPP_Foundations.Model.Paths.Level
import LPP_Foundations.Probability.CoordinateLaw
import Mathlib.Probability.BorelCantelli
import Mathlib.Tactic

/-! A fixed-width strip almost surely cannot support arbitrarily long paths of top weight. -/

public section

open MeasureTheory Set Filter ProbabilityTheory
open scoped BigOperators ENNReal Function

namespace LPPDifferentiability.FinalDraft

private def closedCut (M : ℝ) (J : Finset Lattice) : Set Environment :=
  {ω | ∀ z ∈ J, ω z ≠ M}

private theorem closedCut_eq_inter (M : ℝ) (J : Finset Lattice) :
    closedCut M J =
      ⋂ z ∈ J, (fun ω : Environment => ω z) ⁻¹' ({M} : Set ℝ)ᶜ := by
  ext ω
  simp [closedCut]

private theorem measurableSet_closedCut (M : ℝ) (J : Finset Lattice) :
    MeasurableSet (closedCut M J) := by
  rw [closedCut_eq_inter]
  exact MeasurableSet.iInter fun z => MeasurableSet.iInter fun _ =>
    (measurable_environment_eval z) (measurableSet_singleton M).compl

private theorem closedCut_measure (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (M : ℝ) (J : Finset Lattice) :
    environmentLaw μ (closedCut M J) = ∏ _z ∈ J, μ ({M} : Set ℝ)ᶜ := by
  have heval (z : Lattice) :
      environmentLaw μ ((fun ω : Environment => ω z) ⁻¹' ({M} : Set ℝ)ᶜ) =
        μ ({M} : Set ℝ)ᶜ := by
    rw [← Measure.map_apply (measurable_environment_eval z) (measurableSet_singleton M).compl,
      environmentLaw_map_eval]
  rw [closedCut_eq_inter]
  calc
    _ = ∏ z ∈ J, environmentLaw μ ((fun ω : Environment => ω z) ⁻¹' ({M} : Set ℝ)ᶜ) :=
      (iIndepFun_environment_eval μ).measure_inter_preimage_eq_mul
        J (fun _ _ => (measurableSet_singleton M).compl)
    _ = _ := Finset.prod_congr rfl (fun z _ => heval z)

private theorem iIndepSet_closedCut (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (M : ℝ) (J : ℕ → Finset Lattice) (hJ : Pairwise (Disjoint on J)) :
    iIndepSet (fun k => closedCut M (J k)) (environmentLaw μ) := by
  classical
  apply (iIndepSet_iff_meas_biInter (fun k => measurableSet_closedCut M (J k))).2
  intro s
  have hunion : (⋂ k ∈ s, closedCut M (J k)) = closedCut M (s.biUnion J) := by
    ext ω
    simp only [mem_iInter, closedCut, mem_ofPred_eq, Finset.mem_biUnion]
    constructor
    · rintro h z ⟨k, hk, hz⟩
      exact h k hk z hz
    · intro h k hk z hz
      exact h z ⟨k, hk, hz⟩
  rw [hunion]
  simp_rw [closedCut_measure]
  exact Finset.prod_biUnion (fun i _ j _ hij => hJ hij)

/-- Almost surely every fixed-width strip has a wholly non-top level above any
fixed start level. Its possible future cuts are independent, each with a
positive probability bounded below in terms of the width and the top atom. -/
private theorem ae_exists_closedCut (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (M : ℝ) (hM : μ ({M} : Set ℝ) < 1) (a ρ B : ℝ) (hB : 0 ≤ B) (I : ℤ) :
    ∀ᵐ ω ∂environmentLaw μ, ∃ k : ℕ, ∀ z : Lattice, z.1 + z.2 = I + (k : ℤ) →
      |stripTransverse a z - ρ| ≤ B → ω z ≠ M := by
  have hwidth : ρ - B ≤ ρ + B := by linarith
  choose J hJ hcard using fun k : ℕ =>
    exists_finset_level_interval a (ρ - B) (ρ + B) (I + (k : ℤ)) hwidth
  have hdisjoint : Pairwise (Disjoint on J) := by
    intro i j hij
    refine Finset.disjoint_left.2 fun z hi hj => hij ?_
    have hzi := ((hJ i z).1 hi).1
    have hzj := ((hJ j z).1 hj).1
    omega
  have hmeas (k : ℕ) : MeasurableSet (closedCut M (J k)) :=
    measurableSet_closedCut M (J k)
  have hind := iIndepSet_closedCut μ M J hdisjoint
  -- The bound on each cut size gives one positive lower bound for its probability.
  obtain ⟨K, hK⟩ := exists_nat_ge ((ρ + B) - (ρ - B) + 1)
  let r : ℝ≥0∞ := μ ({M} : Set ℝ)ᶜ
  have hr : r ≠ 0 := fun he => hM.ne ((prob_compl_eq_zero_iff (measurableSet_singleton M)).1 he)
  have hcut_lb (k : ℕ) : r ^ K ≤ environmentLaw μ (closedCut M (J k)) := by
    rw [closedCut_measure, Finset.prod_const]
    change r ^ K ≤ r ^ (J k).card
    have hk : (J k).card ≤ K := by exact_mod_cast (hcard k).trans hK
    exact pow_le_pow_right_of_le_one' prob_le_one hk
  have hsum : ∑' k : ℕ, environmentLaw μ (closedCut M (J k)) = ⊤ := by
    apply top_unique
    calc
      ⊤ = ∑' _k : ℕ, r ^ K := (ENNReal.tsum_const_eq_top_of_ne_zero (pow_ne_zero K hr)).symm
      _ ≤ _ := ENNReal.tsum_le_tsum hcut_lb
  have hfull := measure_limsup_eq_one hmeas hind hsum
  have hlim_meas : MeasurableSet (Filter.limsup (fun k => closedCut M (J k)) atTop) :=
    MeasurableSet.measurableSet_limsup hmeas
  have hae : ∀ᵐ ω ∂environmentLaw μ,
      ω ∈ Filter.limsup (fun k => closedCut M (J k)) atTop :=
    ae_iff.2 ((prob_compl_eq_zero_iff hlim_meas).2 hfull)
  filter_upwards [hae] with ω hω
  rw [Filter.mem_limsup_iff_frequently_mem] at hω
  obtain ⟨k, _, hk⟩ := Filter.frequently_atTop.1 hω 0
  refine ⟨k, fun z hz htrans => hk z ((hJ k z).2 ⟨hz, ?_⟩)⟩
  change |(1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ) - ρ| ≤ B at htrans
  exact ⟨by linarith [(abs_le.1 htrans).1], by linarith [(abs_le.1 htrans).2]⟩

/-- At every fixed-width strip and all signed start levels, almost surely
every sufficiently long confined path has weight strictly below the upper
bound times its length in the discussion of the flat segment, subsection `sub:flatexcluded`. -/
theorem ae_eventually_pathWeight_lt_top_in_fixed_strip
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (M : ℝ) (hupper : ∀ᵐ t ∂μ, t ≤ M) (hnonconst : LPPStatements.NotAPointMass μ)
    (a ρ B : ℝ) (hB : 0 ≤ B) :
    ∀ᵐ ω ∂environmentLaw μ, ∀ I : ℤ, ∃ N : ℕ, ∀ (n : ℕ), N ≤ n →
      ∀ (u : Lattice), u.1 + u.2 = I →
        ∀ (d : ℕ × ℕ), d.1 + d.2 = n → ∀ p : Path u d,
          (∀ i, |stripTransverse a (p.vertex i) - ρ| ≤ B) →
            pathWeight ω p < (n : ℝ) * M := by
  have hbound : ∀ᵐ ω ∂environmentLaw μ, ∀ z : Lattice, ω z ≤ M := by
    apply ae_all_iff.2
    intro z
    apply ae_of_ae_map (p := fun t : ℝ => t ≤ M) (measurable_environment_eval _).aemeasurable
    simpa only [environmentLaw_map_eval] using hupper
  have hcuts := ae_all_iff.2 fun I : ℤ => ae_exists_closedCut μ M (hnonconst M) a ρ B hB I
  filter_upwards [hbound, hcuts] with ω hω hcut I
  obtain ⟨k, hk⟩ := hcut I
  refine ⟨k + 1, fun n hn u hu d hd p hpath => ?_⟩
  -- The chosen cut is visited at time k strictly before the terminal vertex.
  let i : Fin (d.1 + d.2) := ⟨k, by omega⟩
  have hlevel : (p.vertex i.castSucc).1 + (p.vertex i.castSucc).2 = I + (k : ℤ) := by
    rw [p.level, hu]
    rfl
  have hstrict : ω (p.vertex i.castSucc) < M :=
    lt_of_le_of_ne (hω _) (hk _ hlevel (hpath i.castSucc))
  have hsum : (∑ j : Fin (d.1 + d.2), ω (p.vertex j.castSucc)) <
      ∑ _j : Fin (d.1 + d.2), M :=
    Finset.sum_lt_sum (fun j _ => hω (p.vertex j.castSucc)) ⟨i, Finset.mem_univ _, hstrict⟩
  simpa only [pathWeight, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, hd] using hsum

end LPPDifferentiability.FinalDraft
