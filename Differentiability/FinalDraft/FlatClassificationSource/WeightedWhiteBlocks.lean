/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.FlatClassificationSource.ThresholdLaw
public import Differentiability.FinalDraft.FlatClassificationSource.WeightedBlocks
import Differentiability.FinalDraft.FlatClassificationSource.TerminalMark
import all Differentiability.Probability.WhiteBlockBound
import LPP_Foundations.Model.Paths.Level
import LPP_Foundations.Probability.PassageMeasurable
import Mathlib.Tactic

/-! # Probability bounds for passage blocks -/

public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators

namespace LPPDifferentiability.FinalDraft

/-- A path losing less than `δ` has no collected weight below the cutoff. -/
private theorem cutoff_le_collected_of_pathWeight_gt (ω : Environment)
    (hω : ∀ z, ω z ≤ 1) {u : Lattice} {d : ℕ × ℕ} (p : Path u d) (δ : ℝ)
    (hp : ((d.1 + d.2 : ℕ) : ℝ) - δ < pathWeight ω p) (i : Fin (d.1 + d.2)) :
    1 - δ ≤ ω (p.vertex i.castSucc) := by
  classical
  let f (j : Fin (d.1 + d.2)) := ω (p.vertex j.castSucc)
  have hi : i ∈ (Finset.univ : Finset (Fin (d.1 + d.2))) := Finset.mem_univ _
  have hs := Finset.sum_erase_add _ f hi
  have hrest : ∑ j ∈ (Finset.univ.erase i), f j ≤ ((d.1 + d.2 - 1 : ℕ) : ℝ) := by
    calc
      _ ≤ ∑ _ ∈ (Finset.univ.erase i), (1 : ℝ) := Finset.sum_le_sum fun j _ => hω _
      _ = _ := by simp [Finset.card_erase_of_mem hi]
  have hn : (1 : ℕ) ≤ d.1 + d.2 := by have := i.isLt; omega
  rw [Nat.cast_sub hn, Nat.cast_one] at hrest
  change ((d.1 + d.2 : ℕ) : ℝ) - δ < ∑ i, f i at hp
  change 1 - δ ≤ f i
  linarith

/-- A near-optimal passage with a terminal weight at the cutoff gives an open path. -/
private theorem openReach_nearTop_of_passage_gt (ω : Environment)
    (hω : ∀ z, ω z ≤ 1) (u : Lattice) (d : ℕ × ℕ) (δ : ℝ)
    (hG : ((d.1 + d.2 : ℕ) : ℝ) - δ < lastPassage ω u d)
    (hv : 1 - δ ≤ ω (u + ((d.1 : ℤ), (d.2 : ℤ)))) :
    OpenReach (topSites (fun z => nearTopIndicator δ (ω z))) u
      (u + ((d.1 : ℤ), (d.2 : ℤ))) := by
  obtain ⟨p, hp⟩ := exists_pathWeight_eq_lastPassage ω u d
  refine ⟨d, rfl, p, fun i => (mem_topSites_nearTopIndicator_iff ω δ _).mpr ?_⟩
  by_cases hi : i.val + 1 < d.1 + d.2
  · let j : Fin (d.1 + d.2) := ⟨i.val + 1, hi⟩
    have hj : j.castSucc = i.succ := Fin.ext rfl
    rw [← hj]
    exact cutoff_le_collected_of_pathWeight_gt ω hω p δ (hp ▸ hG) j
  · have hfin : i.succ = Fin.last (d.1 + d.2) := Fin.ext (by
      simp only [Fin.val_succ, Fin.val_last]
      have := i.isLt
      omega)
    rw [hfin, p.finish]
    exact hv

/-- The white probability is at most the sum over possible crossing starts of a threshold
half-line tail, divided by the probability of marking a terminal site. -/
theorem white_passage_block_probability_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hle : ∀ᵐ w ∂ν, w ≤ 1) (N : ℕ) (c δ : ℝ) (z : Lattice)
    (hq : 0 < (nearTopDensity ν δ : ℝ)) :
    (environmentLaw ν).real {ω : Environment | ¬ IsBlackPassageBlock ω N c δ z} ≤
      ((N : ℝ) + 1) *
        (environmentLaw (bernoulliMeasure (1 : ℝ) 0 (nearTopDensity ν δ))).real
          {ω : Environment | c * N ≤ (halfLineEdge ω N : ℝ)} /
        (nearTopDensity ν δ : ℝ) := by
  let Δ (j : Fin (N + 1)) := passageBlockDisplacement N j
  let u (i : Fin (N + 1)) := passageBlockStart N z i
  let v (i j : Fin (N + 1)) := u i + (((Δ j).1 : ℤ), ((Δ j).2 : ℤ))
  let W (i j : Fin (N + 1)) := {ω : Environment | c * N ≤ (j.val : ℝ) ∧
    (N : ℝ) - δ < lastPassage ω (u i) (Δ j)}
  let H := {ω : Environment | c * N ≤ (halfLineEdge ω N : ℝ)}
  let F (ω : Environment) : Environment := fun x => nearTopIndicator δ (ω x)
  let q : unitInterval := nearTopDensity ν δ
  let P := environmentLaw ν
  have hFH : MeasurableSet (F ⁻¹' H) :=
    (measurable_coordinatewise_environment_map _
      (show Measurable (nearTopIndicator δ) from measurable_const.indicator measurableSet_Ici))
        (measurableSet_halfLine_ge c N)
  have hω : ∀ᵐ ω ∂P, ∀ x : Lattice, ω x ≤ 1 := ae_all_iff.mpr fun x =>
    ae_of_ae_map (measurable_environment_eval x).aemeasurable
      (by rwa [environmentLaw_map_eval ν x])
  have hP (i : Fin (N + 1)) :
      P.real (⋃ j, W i j) ≤ (environmentLaw (bernoulliMeasure (1 : ℝ) 0 q)).real H / (q : ℝ) := by
    let m := (u i).1 + (u i).2 + (N : ℤ) - 1
    have hA (j : Fin (N + 1)) : MeasurableSet[levelsAtMost m] (W i j) := by
      by_cases hj : c * N ≤ (j.val : ℝ)
      · have hlev : ((Δ j).1 : ℤ) + ((Δ j).2 : ℤ) = (N : ℤ) := by
          exact_mod_cast passageBlockDisplacement_level N j
        have hm : (u i).1 + (u i).2 + ((Δ j).1 : ℤ) + ((Δ j).2 : ℤ) - 1 = m := by
          dsimp only [m]
          omega
        have hmeas := measurable_lastPassage_before_terminal (u i) (Δ j)
        rw [hm] at hmeas
        simpa only [W, hj, true_and] using measurableSet_lt measurable_const hmeas
      · simp only [W, hj, false_and, ofPred_false]
        exact @MeasurableSet.empty Environment (levelsAtMost m)
    have hv (j : Fin (N + 1)) : m < (v i j).1 + (v i j).2 := by
      have hlen : ((Δ j).1 : ℤ) + ((Δ j).2 : ℤ) = (N : ℤ) := by
        exact_mod_cast passageBlockDisplacement_level N j
      simp only [m, v, Prod.fst_add, Prod.snd_add]
      omega
    have hI := measure_union_mul_le_terminal_mark ν m N (W i) hA (v i) hv
      (Ici (1 - δ)) measurableSet_Ici
    have hsub : (⋃ j, W i j ∩ (fun ω : Environment => ω (v i j)) ⁻¹' Ici (1 - δ))
        ≤ᵐ[P] (fun ω : Environment => fun y => ω (u i + y)) ⁻¹' (F ⁻¹' H) := by
      filter_upwards [hω] with ω hω hmem
      obtain ⟨j, hj, hlast⟩ := mem_iUnion.mp hmem
      have hlen : (Δ j).1 + (Δ j).2 = N := passageBlockDisplacement_level N j
      have hjG := hj.2
      have hdrive := hj.1
      have hd : (v i j).1 - (u i).1 + ((v i j).2 - (u i).2) = (N : ℤ) := by
        have hlenZ : (((Δ j).1 : ℕ) : ℤ) + (((Δ j).2 : ℕ) : ℤ) = N := by
          exact_mod_cast hlen
        simp only [v, Prod.fst_add, Prod.snd_add]
        omega
      have hc : c * N ≤ (((v i j).1 - (u i).1 : ℤ) : ℝ) := by
        simpa [v, Δ, passageBlockDisplacement] using hdrive
      have hpass : (((Δ j).1 + (Δ j).2 : ℕ) : ℝ) - δ < lastPassage ω (u i) (Δ j) := by
        rw [hlen]
        exact hjG
      exact le_halfLineEdge_shift (F ω) N c (u i) (v i j) hd hc
        (openReach_nearTop_of_passage_gt ω hω (u i) (Δ j) δ hpass hlast)
    have hprob := hI.trans (measure_mono_ae hsub)
    have hto := ENNReal.toReal_mono (measure_ne_top _ _) hprob
    rw [ENNReal.toReal_mul] at hto
    apply (le_div_iff₀ hq).mpr
    change P.real (⋃ j, W i j) * ν.real (Ici (1 - δ)) ≤ _
    refine hto.trans_eq ?_
    change P.real ((fun ω : Environment => fun y => ω (u i + y)) ⁻¹' (F ⁻¹' H)) = _
    rw [measureReal_shift_preimage ν (u i) hFH]
    rw [← map_measureReal_apply (measurable_coordinatewise_environment_map _
      (show Measurable (nearTopIndicator δ) from measurable_const.indicator measurableSet_Ici))
      (measurableSet_halfLine_ge c N)]
    rw [map_nearTopIndicator_environmentLaw]
  have hW : {ω : Environment | ¬ IsBlackPassageBlock ω N c δ z} =
      ⋃ i, ⋃ j, W i j := by
    ext ω
    classical
    simp only [mem_ofPred_eq, IsBlackPassageBlock, not_forall, not_le, mem_iUnion, W, u, Δ, exists_prop]
  rw [hW]
  calc
    _ ≤ ∑ i : Fin (N + 1), P.real (⋃ j, W i j) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _ : Fin (N + 1), (environmentLaw (bernoulliMeasure (1 : ℝ) 0 q)).real H / (q : ℝ) :=
      Finset.sum_le_sum fun i _ => hP i
    _ = _ := by simp [q, H, div_eq_mul_inv, mul_assoc]

end LPPDifferentiability.FinalDraft
