/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.FlatClassificationSource.WeightedBlocks
public import Differentiability.Probability.LevelSigma
import all Differentiability.Probability.LevelIndependence
import all Differentiability.Probability.AugmentedMeasurability
import LPP_Foundations.Model.Paths.Level
import LPP_Foundations.Probability.PassageMeasurable
import Mathlib.Tactic

/-! # Terminal marks for passage events -/

public section

open MeasureTheory ProbabilityTheory Set Filter Function
open scoped ENNReal BigOperators

namespace LPPDifferentiability.FinalDraft

/-- A passage reads the levels strictly below its terminal level. -/
theorem measurable_lastPassage_before_terminal (u : Lattice) (d : ℕ × ℕ) :
    Measurable[levelsAtMost (u.1 + u.2 + (d.1 : ℤ) + (d.2 : ℤ) - 1)]
      (fun ω : Environment => lastPassage ω u d) := by
  let m := u.1 + u.2 + (d.1 : ℤ) + (d.2 : ℤ) - 1
  let F (ω : Environment) (z : Lattice) := if z.1 + z.2 ≤ m then ω z else 0
  have hF : Measurable[levelsAtMost m] F := by
    refine measurable_of_eval_coords (mΩ := levelsAtMost m) F ?_
    intro z
    by_cases hz : z.1 + z.2 ≤ m
    · simpa only [F, ite_eq_left hz] using measurable_site m hz
    · simp only [F, ite_eq_right hz]
      exact measurable_const
  have heq : (fun ω : Environment => lastPassage (F ω) u d) =
      fun ω : Environment => lastPassage ω u d := by
    funext ω
    apply lastPassage_eq_of_agree_on_collected
    intro p i
    have hl := p.level i.castSucc
    have hi := i.isLt
    simp only [Fin.val_castSucc] at hl
    simp only [F, ite_eq_left (show (p.vertex i.castSucc).1 + (p.vertex i.castSucc).2 ≤ m by
      dsimp only [m]
      omega)]
  rw [← heq]
  exact (measurable_lastPassage u d).comp hF

/-- Thinning a finite union by marks on the next level retains at least the common mark
probability times the mass of the union. The first successful event can be selected using
only the lower levels. -/
theorem measure_union_mul_le_terminal_mark
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (m : ℤ) (n : ℕ)
    (A : Fin (n + 1) → Set Environment) (hA : ∀ i, MeasurableSet[levelsAtMost m] (A i))
    (v : Fin (n + 1) → Lattice) (hv : ∀ i, m < (v i).1 + (v i).2)
    (K : Set ℝ) (hK : MeasurableSet K) :
    environmentLaw ν (⋃ i, A i) * ν K ≤
      environmentLaw ν (⋃ i, A i ∩ (fun ω : Environment => ω (v i)) ⁻¹' K) := by
  let B (i : Fin (n + 1)) := (fun ω : Environment => ω (v i)) ⁻¹' K
  let F := disjointed A
  have hDis : Pairwise (Disjoint on F) := disjoint_disjointed A
  have hFM (i : Fin (n + 1)) : MeasurableSet[levelsAtMost m] (F i) := by
    change MeasurableSet[levelsAtMost m] (disjointed A i)
    rw [disjointed_eq_inter_compl]
    exact (hA i).inter (MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun _ => (hA j).compl)
  have hBM : ∀ i, MeasurableSet[levelsAbove m] (B i) := fun i =>
    (Measurable.of_comap_le (coordSigma_le_levelsAbove m (v i) (hv i))) hK
  have hi := (iIndepFun_environment_eval ν).iIndep
  have hindep : Indep (levelsAtMost m) (levelsAbove m) (environmentLaw ν) := by
    apply indep_iSup_of_disjoint coordSigma_le hi
    exact Set.disjoint_left.2 fun z ha hb =>
      (not_lt_of_ge (show z.1 + z.2 ≤ m from ha)) (show m < z.1 + z.2 from hb)
  have hterm (i : Fin (n + 1)) :
      environmentLaw ν (F i ∩ B i) = environmentLaw ν (F i) * ν K := by
    have hB : environmentLaw ν (B i) = ν K := by
      calc
        _ = ((environmentLaw ν).map (fun ω : Environment => ω (v i))) K :=
          (Measure.map_apply (measurable_environment_eval _) hK).symm
        _ = _ := congrArg (fun μ : Measure ℝ => μ K) (environmentLaw_map_eval ν (v i))
    rw [(Indep_iff _ _ _).mp hindep _ _ (hFM i) (hBM i), hB]
  have hFdis : Pairwise (Disjoint on fun i => F i ∩ B i) :=
    fun i j hij => (hDis hij).mono inter_subset_left inter_subset_left
  have hFM' : ∀ i, MeasurableSet (F i) := fun i => levelsAtMost_le m _ (hFM i)
  have hFBM : ∀ i, MeasurableSet (F i ∩ B i) :=
    fun i => (hFM' i).inter ((measurable_environment_eval _) hK)
  calc
    _ = environmentLaw ν (⋃ i, F i) * ν K := by rw [iUnion_disjointed]
    _ = environmentLaw ν (⋃ i, F i ∩ B i) := by
      rw [measure_iUnion hDis hFM', measure_iUnion hFdis hFBM]
      simp_rw [hterm]
      exact (ENNReal.tsum_mul_right).symm
    _ ≤ _ := measure_mono (iUnion_mono fun i => inter_subset_inter_left _ (disjointed_le A i))

end LPPDifferentiability.FinalDraft
