/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.FlatDensitySource.ContinuationGain
public import Differentiability.FinalDraft.FlatDensitySource.MeanRates
import all Differentiability.Probability.RightBlockGain
import all Differentiability.Probability.HalfLineEdgeDeviation
import Differentiability.Probability.LevelIndependence
import Differentiability.Model.OrientedPercolationLaws
import Mathlib.Probability.Independence.Integration

/-! Durrett's expected edge comparison from the stopped continuation and the split probability. -/

@[expose] public section

open Filter Function MeasureTheory ProbabilityTheory Set

namespace LPPDifferentiability.FinalDraft

/-- The gain from a single added site only uses uniforms on levels above zero. -/
private theorem halfLineOneSiteGain_congr (p : unitInterval) (k : ℕ) (u v : Environment)
    (h : ∀ z : Lattice, 0 < z.1 + z.2 → u z = v z) :
    halfLineOneSiteGain (thresholdSiteEnvironment p u) k =
      halfLineOneSiteGain (thresholdSiteEnvironment p v) k := by
  have hreach (S : Set Lattice) (hS : S ⊆ levelSet 0) :
      openReachSet (topSites (thresholdSiteEnvironment p u)) S k =
        openReachSet (topSites (thresholdSiteEnvironment p v)) S k := by
    refine openReachSet_congr _ _ _ 0 k hS (fun z hz _ => ?_)
    rw [mem_topSites_thresholdSiteEnvironment_iff, mem_topSites_thresholdSiteEnvironment_iff,
      h z hz]
  have hS : antidiagHalfLine ∪ antidiagRightBlock 1 ⊆ levelSet 0 :=
    union_subset antidiagHalfLine_subset_levelSet fun _ hz => hz.1
  unfold halfLineOneSiteGain halfLineEdge openEdge
  rw [hreach _ hS, hreach _ antidiagHalfLine_subset_levelSet]

/-- The one-site gain is measurable as a difference of two edges. -/
private theorem measurable_halfLineOneSiteGain (k : ℕ) :
    Measurable (fun ω : Environment => halfLineOneSiteGain ω k) := by
  have hS : antidiagHalfLine ∪ antidiagRightBlock 1 ⊆ levelSet 0 :=
    union_subset antidiagHalfLine_subset_levelSet fun _ hz => hz.1
  have hZ := measurable_openEdge_levelsAtMost _ 0 hS k
  have hR : Measurable (fun z : ℤ => (z : ℝ)) := Measurable.of_discrete
  exact (hR.comp (hZ.mono (levelsAtMost_le _) le_rfl)).sub
    (hR.comp (measurable_halfLineEdge k))

/-- On a first-split fiber, the translated future gain contributes exactly the
probability of that fiber, since its law is independent of the split history. -/
private theorem integral_firstSplit_fiber_gain (p q : unitInterval) (hp : 0 < (p : ℝ))
    (m k : ℕ) :
    let D := (firstEdgeSplitAt p q m).indicator (fun u =>
      halfLineOneSiteGain (thresholdSiteEnvironment p (fun z => u (firstSplitCenter q m u + z))) k)
    Integrable D siteUniformLaw ∧
      (∫ u, D u ∂siteUniformLaw) = siteUniformLaw.real (firstEdgeSplitAt p q m) := by
  classical
  dsimp only
  let A := firstEdgeSplitAt p q m
  let G : Environment → ℝ := A.indicator (fun _ => 1)
  let F (u : Environment) := halfLineOneSiteGain (thresholdSiteEnvironment p u) k
  let F' (u : Environment) :=
    halfLineOneSiteGain (thresholdSiteEnvironment p (fun z => u (firstSplitCenter q m u + z))) k
  have hAlow := measurableSet_firstEdgeSplitAt_levels p q m
  have hA : MeasurableSet A := levelsAtMost_le _ _ hAlow
  have hG : Measurable[levelsAtMost (m : ℤ)] G := measurable_const.indicator hAlow
  have hF : Measurable F :=
    (measurable_halfLineOneSiteGain k).comp (measurable_thresholdSiteEnvironment p)
  have hFi : Integrable F siteUniformLaw := by
    have h : Integrable (fun ω => halfLineOneSiteGain ω k)
        (siteUniformLaw.map (thresholdSiteEnvironment p)) := by
      rw [map_siteUniformLaw_thresholdSiteEnvironment]
      exact integrable_gain _ (bernoulli_singleton_one_pos p hp) 1 k
    exact h.comp_measurable (measurable_thresholdSiteEnvironment p)
  have hFe : (∫ u, F u ∂siteUniformLaw) = 1 := by
    rw [show (∫ u, F u ∂siteUniformLaw) =
      ∫ ω, halfLineOneSiteGain ω k ∂siteUniformLaw.map (thresholdSiteEnvironment p) from
        (integral_map (measurable_thresholdSiteEnvironment p).aemeasurable
          (measurable_halfLineOneSiteGain k).aestronglyMeasurable).symm,
      map_siteUniformLaw_thresholdSiteEnvironment]
    simpa only [halfLineOneSiteGain, Nat.cast_one] using
      integral_halfLine_rightBlock_gain _ (bernoulli_singleton_one_pos p hp) 1 k
  obtain ⟨hInd, hLaw⟩ := indepFun_identDistrib_shift_of_levelsAtMost siteUniformMarginal (m : ℤ)
    (firstSplitCenter q m) (measurable_firstSplitCenter_levels q m) (firstSplitCenter_level q m)
    F hF (halfLineOneSiteGain_congr p k) G hG
  change IndepFun G F' siteUniformLaw at hInd
  have hId : IdentDistrib F' F siteUniformLaw siteUniformLaw := hLaw
  have hFi' := hId.symm.integrable_snd hFi
  have hGm : Measurable G := hG.mono (levelsAtMost_le _) le_rfl
  refine ⟨hFi'.indicator hA, ?_⟩
  have hprod : A.indicator F' = fun u => G u * F' u := by
    ext u
    by_cases hu : u ∈ A <;> simp [G, hu]
  change (∫ u, A.indicator F' u ∂siteUniformLaw) = siteUniformLaw.real A
  rw [hprod]
  change (∫ u, G u * F' u ∂siteUniformLaw) = siteUniformLaw.real A
  rw [hInd.integral_fun_mul_eq_mul_integral hGm.aestronglyMeasurable
      hId.aestronglyMeasurable_fst, hId.integral_eq, hFe, mul_one]
  exact integral_indicator_one hA

/-- The expected gain of the stopped continuation is at least the probability
that a split has occurred by the observation level. -/
theorem real_measure_split_le_integral_firstSplitContinuation_gap
    {p q : unitInterval} (hp : 0 < (p : ℝ)) (hpq : p ≤ q) (n : ℕ) :
    let D (u : Environment) :=
      (halfLineEdge (firstSplitContinuationEnvironment p q u) n : ℝ) -
        halfLineEdge (thresholdSiteEnvironment p u) n
    Integrable D siteUniformLaw ∧
      siteUniformLaw.real (noEdgeSplitThrough p q n)ᶜ ≤ ∫ u, D u ∂siteUniformLaw := by
  classical
  dsimp only
  let D (u : Environment) :=
    (halfLineEdge (firstSplitContinuationEnvironment p q u) n : ℝ) -
      halfLineEdge (thresholdSiteEnvironment p u) n
  let A (i : Fin (n + 1)) := firstEdgeSplitAt p q i
  let J (i : Fin (n + 1)) (u : Environment) :=
    halfLineOneSiteGain
      (thresholdSiteEnvironment p (fun z => u (firstSplitCenter q i u + z))) (n - i)
  let C (i : Fin (n + 1)) := (A i).indicator (J i)
  have hmeas : ∀ i, MeasurableSet (A i) := fun i =>
    levelsAtMost_le _ _ (measurableSet_firstEdgeSplitAt_levels p q i)
  have hC (i : Fin (n + 1)) := integral_firstSplit_fiber_gain p q hp i (n - i)
  have hAE := ae_thresholdHalfLine_nonempty p hp
  have hDnonneg : ∀ (u : Environment), (openReachSet (topSites
      (thresholdSiteEnvironment p u)) antidiagHalfLine n).Nonempty → 0 ≤ D u := by
    intro u hu
    exact sub_nonneg.mpr (Int.cast_le.mpr (halfLineEdge_mono_of_topSites_subset n hu
      (firstSplitContinuation_topSites_bounds hpq u).1))
  have hm : Measurable (fun ω : Environment => (halfLineEdge ω n : ℝ)) :=
    (Measurable.of_discrete (f := fun z : ℤ => (z : ℝ))).comp (measurable_halfLineEdge n)
  have hDm : Measurable D :=
    (hm.comp (measurable_firstSplitContinuationEnvironment p q)).sub
      (hm.comp (measurable_thresholdSiteEnvironment p))
  have hpInt : Integrable (fun u => (halfLineEdge (thresholdSiteEnvironment p u) n : ℝ))
      siteUniformLaw := by
    have hi : Integrable (fun ω => (halfLineEdge ω n : ℝ))
        (siteUniformLaw.map (thresholdSiteEnvironment p)) := by
      rw [map_siteUniformLaw_thresholdSiteEnvironment]
      exact integrable_halfLineEdge _ (bernoulli_singleton_one_pos p hp) n
    exact hi.comp_measurable (measurable_thresholdSiteEnvironment p)
  have hDI : Integrable D siteUniformLaw := by
    refine Integrable.mono' ((integrable_const (n : ℝ)).sub hpInt)
      hDm.aestronglyMeasurable ?_
    filter_upwards [hAE] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (hDnonneg u (hu n))]
    exact sub_le_sub_right (Int.cast_le.mpr (halfLineEdge_le _ n)) _
  refine ⟨hDI, ?_⟩
  have hsum : ∀ᵐ u ∂siteUniformLaw, (∑ i, C i u) ≤ D u := by
    filter_upwards [hAE] with u hu
    by_cases hsplit : ∃ i, u ∈ A i
    · obtain ⟨i, hi⟩ := hsplit
      have hsum_eq : (∑ j, C j u) = C i u := by
        refine Finset.sum_eq_single i (fun j _ hj => ?_) (by simp)
        exact indicator_of_notMem (fun huj => hj (Fin.ext (firstEdgeSplitAt_unique huj hi))) _
      rw [hsum_eq, show C i u = J i u from indicator_of_mem hi _]
      have h := halfLineOneSiteGain_le_firstSplitContinuation_gap hpq hi (n - i) hu
      rwa [Nat.add_sub_cancel' (Nat.le_of_lt_succ i.isLt)] at h
    · have hzero : ∀ i, C i u = 0 := fun i =>
        indicator_of_notMem (fun hi => hsplit ⟨i, hi⟩) _
      simp only [hzero, Finset.sum_const_zero]
      exact hDnonneg u (hu n)
  have hI := integral_mono_ae (integrable_finsetSum Finset.univ (fun i _ => (hC i).1)) hDI hsum
  rw [integral_finsetSum _ (fun i _ => (hC i).1)] at hI
  simp_rw [(hC _).2] at hI
  rw [compl_noEdgeSplitThrough_eq_iUnion p q n, measureReal_iUnion_fintype
    (fun i j hij => Set.disjoint_left.mpr fun _ hi hj =>
      hij (Fin.ext (firstEdgeSplitAt_unique hi hj))) hmeas]
  exact hI

/-- The difference of the two Bernoulli expected edges is at least the probability
of a split by level n. Together with the geometric bound this gives equation (14)
of Durrett's argument, in first coordinates for the oriented site model. -/
theorem one_sub_pow_le_expectedBernoulliHalfLineEdge_sub {p q : unitInterval}
    (hp : 0 < (p : ℝ)) (hpq : p ≤ q) (n : ℕ) :
    1 - (1 - ((q : ℝ) - (p : ℝ))) ^ n ≤
      expectedBernoulliHalfLineEdge q n - expectedBernoulliHalfLineEdge p n := by
  let E (r : unitInterval) (u : Environment) := (halfLineEdge (thresholdSiteEnvironment r u) n : ℝ)
  let D (u : Environment) :=
    (halfLineEdge (firstSplitContinuationEnvironment p q u) n : ℝ) - E p u
  have hmeas : MeasurableSet (noEdgeSplitThrough p q n) :=
    levelsAtMost_le _ _ (measurableSet_noEdgeSplitThrough_levels p q n)
  have hprob := real_measure_noEdgeSplitThrough_le hp hpq n
  obtain ⟨hDI, hD⟩ := real_measure_split_le_integral_firstSplitContinuation_gap hp hpq n
  have hm : Measurable (fun ω : Environment => (halfLineEdge ω n : ℝ)) :=
    (Measurable.of_discrete (f := fun z : ℤ => (z : ℝ))).comp (measurable_halfLineEdge n)
  have hEI (r : unitInterval) (hr : 0 < (r : ℝ)) : Integrable (E r) siteUniformLaw := by
    have hi : Integrable (fun ω => (halfLineEdge ω n : ℝ))
        (siteUniformLaw.map (thresholdSiteEnvironment r)) := by
      rw [map_siteUniformLaw_thresholdSiteEnvironment]
      exact integrable_halfLineEdge _ (bernoulli_singleton_one_pos r hr) n
    exact hi.comp_measurable (measurable_thresholdSiteEnvironment r)
  have hE (r : unitInterval) : ∫ u, E r u ∂siteUniformLaw = expectedBernoulliHalfLineEdge r n := by
    unfold expectedBernoulliHalfLineEdge
    rw [← map_siteUniformLaw_thresholdSiteEnvironment r]
    exact (integral_map (measurable_thresholdSiteEnvironment r).aemeasurable
      hm.aestronglyMeasurable).symm
  have hAE : D ≤ᵐ[siteUniformLaw] E q - E p := by
    filter_upwards [ae_thresholdHalfLine_nonempty p hp] with u hu
    have h := firstSplitContinuation_topSites_bounds hpq u
    exact sub_le_sub_right (Int.cast_le.mpr (halfLineEdge_mono_of_topSites_subset n
      ((hu n).mono (openReachSet_mono h.1 subset_rfl n)) h.2)) _
  have hbound := integral_mono_ae hDI ((hEI q (hp.trans_le hpq)).sub (hEI p hp)) hAE
  change (∫ u, D u ∂siteUniformLaw) ≤ (∫ u, E q u - E p u ∂siteUniformLaw) at hbound
  rw [integral_sub (hEI q (hp.trans_le hpq)) (hEI p hp), hE, hE] at hbound
  rw [probReal_compl_eq_one_sub hmeas] at hD
  exact ((sub_le_sub_left hprob 1).trans hD).trans hbound

end LPPDifferentiability.FinalDraft
