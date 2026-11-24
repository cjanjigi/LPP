/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.FlatTop.RestartedHalfLine
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Differentiability.Model.OrientedPercolationLaws
import Differentiability.Probability.AugmentedMeasurability
import Differentiability.Probability.HalfLineEdge
import Mathlib.Probability.Independence.InfinitePi
import ProbabilityBasics.Frozen.Foundations.Liggett.Theorem110

/-! The consecutive restarted blocks have a product law, so the half-line
edge array satisfies Liggett's subadditive convergence theorem. -/

public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators Topology

namespace LPPDifferentiability.FinalDraft

/-- The one-block law is the law of the half-line edge at its duration. -/
private theorem restartedHalfLineEdge_identDistrib (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (m k : ℕ) :
    IdentDistrib (restartedHalfLineEdge m k) (fun ω => halfLineEdge ω k)
      (environmentLaw ν) (environmentLaw ν) := by
  have h := (restartedHalfLineEdge_indepFun_identDistrib_row ν m
    (fun _ => (0 : ℤ)) measurable_const).2
  exact h.comp (measurable_pi_apply k)

/-- Consecutive restarted blocks are independent. Each earlier block is
measurable through the beginning of the last block in any finite test. -/
private theorem iIndepFun_restartedHalfLineEdge_blocks (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (k : ℕ) :
    iIndepFun (fun j => restartedHalfLineEdge ((j + 1) * k) k) (environmentLaw ν) := by
  classical
  let X (j : ℕ) := restartedHalfLineEdge ((j + 1) * k) k
  rw [iIndepFun_iff]
  intro J s
  induction J using Finset.induction_on_max with
  | empty =>
    intro _
    simp
  | insert j J hlt ih =>
    intro hs
    have hj : j ∉ J := fun hj => (lt_irrefl j) (hlt j hj)
    have hJ (i : ℕ) (hi : i ∈ J) :
        MeasurableSet[MeasurableSpace.comap (X i) inferInstance] (s i) :=
      hs i (Finset.mem_insert_of_mem hi)
    let A : Set Environment := ⋂ i ∈ J, s i
    let m := (j + 1) * k
    have hA : MeasurableSet[levelsAtMost (m : ℤ)] A := by
      apply Finset.measurableSet_biInter
      intro i hi
      obtain ⟨B, hB, hpre⟩ := MeasurableSpace.measurableSet_comap.mp (hJ i hi)
      have htime : (((i + 1) * k + k : ℕ) : ℤ) ≤ (m : ℤ) := by
        exact_mod_cast (show (i + 1) * k + k ≤ m by
          rw [← Nat.succ_mul]
          exact Nat.mul_le_mul_right k (by dsimp [m]; have := hlt i hi; omega))
      rw [← hpre]
      exact ((measurable_restartedHalfLineEdge_levelsAtMost ((i + 1) * k) k).mono
        (levelsAtMost_mono htime) le_rfl) hB
    let G : Environment → ℝ := A.indicator 1
    have hG : Measurable[levelsAtMost (m : ℤ)] G := measurable_const.indicator hA
    have hGA : G ⁻¹' ({1} : Set ℝ) = A := by
      ext ω
      simp [G, indicator_apply]
    obtain ⟨B, hB, hpre⟩ :=
      MeasurableSpace.measurableSet_comap.mp (hs j (Finset.mem_insert_self j J))
    have hind := (restartedHalfLineEdge_indepFun_identDistrib_row ν m G hG).1
    have hpair := (indepFun_iff_measure_inter_preimage_eq_mul.mp
      (hind.comp measurable_id (measurable_pi_apply k))) {1} B
      (measurableSet_singleton _) hB
    change environmentLaw ν (G ⁻¹' ({1} : Set ℝ) ∩ X j ⁻¹' B) =
      environmentLaw ν (G ⁻¹' ({1} : Set ℝ)) * environmentLaw ν (X j ⁻¹' B) at hpair
    rw [hGA, hpre] at hpair
    rw [Finset.set_biInter_insert, Finset.prod_insert hj, ← ih hJ]
    simpa only [A, inter_comm (s j), mul_comm (environmentLaw ν (s j))] using hpair

/-- The stationary law of consecutive restarted blocks in the real-valued array. -/
private theorem stationary_restartedHalfLineEdge_blocks (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (k : ℕ) :
    ProbabilityBasics.IsStationaryProcess (environmentLaw ν)
      (fun j ω => (restartedHalfLineEdge ((j + 1) * k) k ω : ℝ)) := by
  let X (j : ℕ) := restartedHalfLineEdge ((j + 1) * k) k
  have hX (j : ℕ) : Measurable (X j) :=
    (measurable_restartedHalfLineEdge_levelsAtMost ((j + 1) * k) k).mono
      (levelsAtMost_le _) le_rfl
  have hI : iIndepFun X (environmentLaw ν) := iIndepFun_restartedHalfLineEdge_blocks ν k
  have hid : IdentDistrib (fun ω j => X (j + 1) ω) (fun ω j => X j ω)
      (environmentLaw ν) (environmentLaw ν) := by
    refine ⟨(Measurable.of_eval fun j => hX (j + 1)).aemeasurable,
      (Measurable.of_eval hX).aemeasurable, ?_⟩
    have hI' := hI.precomp (show Function.Injective (fun j : ℕ => j + 1) from Nat.succ_injective)
    rw [hI'.map_fun_eq_infinitePi_map (fun j => hX (j + 1)),
      hI.map_fun_eq_infinitePi_map hX]
    congr 1
    funext j
    exact (restartedHalfLineEdge_identDistrib ν ((j + 1 + 1) * k) k).map_eq.trans
      (restartedHalfLineEdge_identDistrib ν ((j + 1) * k) k).map_eq.symm
  exact hid.comp (Measurable.of_eval fun j =>
    (Measurable.of_discrete (f := fun x : ℤ => (x : ℝ))).comp (measurable_pi_apply j))

/-- The edge of the initial half-line has first coordinate zero. -/
private theorem halfLineEdge_zero (ω : Environment) : halfLineEdge ω 0 = 0 := by
  apply le_antisymm (halfLineEdge_le ω 0)
  unfold halfLineEdge openEdge
  rw [openReachSet_zero]
  exact le_maxFirst _ bddAbove_fst_antidiagHalfLine (show (0 : Lattice) ∈ antidiagHalfLine by
    simp [antidiagHalfLine])

/-- If the expected rates are bounded below, the half-line edge has a finite
almost sure and integrable limit. The expected limit is the infimum of its
expected rates. -/
theorem exists_halfLineEdge_limit_of_bddBelow (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hν : 0 < ν {1})
    (hbd : BddBelow (Set.range fun n : ℕ =>
      (∫ ω, (halfLineEdge ω (n + 1) : ℝ) ∂environmentLaw ν) / ((n : ℝ) + 1))) :
    ∃ β : ℝ, IsGLB (Set.range fun n : ℕ =>
      (∫ ω, (halfLineEdge ω (n + 1) : ℝ) ∂environmentLaw ν) / ((n : ℝ) + 1)) β ∧
      ∃ limit : Environment → ℝ, Integrable limit (environmentLaw ν) ∧
        (∀ᵐ ω ∂environmentLaw ν,
          Tendsto (fun n : ℕ => (halfLineEdge ω n : ℝ) / (n : ℝ)) atTop (𝓝 (limit ω))) ∧
        (∫ ω, limit ω ∂environmentLaw ν) = β := by
  let X (m n : ℕ) (ω : Environment) : ℝ := restartedHalfLineEdge m (n - m) ω
  have hX0 (n : ℕ) (ω : Environment) : X 0 n ω = (halfLineEdge ω n : ℝ) := by
    simp only [X, restartedHalfLineEdge, halfLineEdge_zero, Nat.sub_zero, Nat.cast_zero, sub_self]
    change (halfLineEdge (fun z => ω ((0 : Lattice) + z)) n : ℝ) = _
    simp only [zero_add]
  have hsub : ProbabilityBasics.Liggett.LiggettSubadditive (environmentLaw ν) X := by
    intro m n _ hmn
    filter_upwards [ae_halfLineEdge_add_le_restartedHalfLineEdge ν hν m (n - m)] with ω hω
    rw [Nat.add_sub_cancel' hmn.le] at hω
    rw [hX0, hX0]
    change (halfLineEdge ω n : ℝ) ≤
      (halfLineEdge ω m : ℝ) + (restartedHalfLineEdge m (n - m) ω : ℝ)
    exact_mod_cast hω
  have hrows : ProbabilityBasics.Liggett.LiggettRowLaws (environmentLaw ν) X := by
    intro m
    have hrow (r : ℕ) := (restartedHalfLineEdge_indepFun_identDistrib_row ν r
      (fun _ => (0 : ℤ)) measurable_const).2
    have h := ((hrow (m + 1)).trans (hrow m).symm).comp
      (Measurable.of_eval fun j => (Measurable.of_discrete (f := fun x : ℤ => (x : ℝ))).comp
        (measurable_pi_apply (j + 1)))
    simpa only [X, Nat.add_sub_cancel_left, Function.comp_def] using h
  have hstat : ProbabilityBasics.Liggett.LiggettBlockStationary (environmentLaw ν) X := by
    intro k _
    have htime (j : ℕ) : (j + 2) * k - (j + 1) * k = k := by
      rw [show (j + 2) * k = (j + 1) * k + k from Nat.succ_mul (j + 1) k]
      omega
    unfold ProbabilityBasics.Liggett.liggettBlockProcess
    simpa only [X, htime] using stationary_restartedHalfLineEdge_blocks ν k
  have hmoment : ProbabilityBasics.Liggett.LiggettMomentCondition (environmentLaw ν) X := by
    obtain ⟨b, hb⟩ := hbd
    refine ⟨fun n _ => (integrable_halfLineEdge ν hν n).congr
      (Eventually.of_forall fun ω => (hX0 n ω).symm), -b, ?_⟩
    intro n hn
    have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    have hn' : n - 1 + 1 = n := Nat.sub_add_cancel hn
    have h := hb (mem_range_self (n - 1))
    have heq : (((n - 1 : ℕ) : ℝ) + 1) = (n : ℝ) := by exact_mod_cast hn'
    rw [hn', heq] at h
    simpa only [hX0, neg_mul, neg_neg] using (le_div_iff₀ hnR).mp h
  obtain ⟨β, _, hβ, limit, _, hLI, hL, _, hE, _⟩ :=
    ProbabilityBasics.Liggett.liggett_subadditive_ergodic (environmentLaw ν)
      X hsub hrows hstat hmoment
  have hset : ((fun n : ℕ => (∫ ω, X 0 n ω ∂environmentLaw ν) / n) '' Ioi 0) =
      Set.range (fun n : ℕ =>
        (∫ ω, (halfLineEdge ω (n + 1) : ℝ) ∂environmentLaw ν) / ((n : ℝ) + 1)) := by
    ext a
    constructor
    · rintro ⟨n, hn, rfl⟩
      have hns : n - 1 + 1 = n := Nat.sub_add_cancel (show 1 ≤ n from hn)
      refine ⟨n - 1, ?_⟩
      have heq : (((n - 1 : ℕ) : ℝ) + 1) = (n : ℝ) := by exact_mod_cast hns
      simp only [hns, heq, hX0]
    · rintro ⟨n, rfl⟩
      exact ⟨n + 1, Nat.succ_pos n, by simp only [hX0, Nat.cast_add, Nat.cast_one]⟩
  rw [hset] at hβ
  exact ⟨β, hβ, limit, hLI, by simpa only [hX0] using hL, hE⟩

end LPPDifferentiability.FinalDraft
