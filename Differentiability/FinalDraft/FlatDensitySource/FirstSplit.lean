/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.FlatTopRates.RightContinuity
public import Differentiability.Probability.HalfLineEdge
import all Differentiability.FinalDraft.FlatTop.HalfLineConvergence
import all Differentiability.Probability.HalfLineEdgeDeviation
import all Differentiability.Probability.AugmentedMeasurability
import Differentiability.Model.OrientedPercolationLaws

/-! Durrett's first split and the site field that continues at the lower density after it. -/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LPPDifferentiability.FinalDraft

/-- At this level the higher-density half-line edge is strictly farther right. -/
def edgeSplit (p q : unitInterval) (n : ℕ) : Set Environment :=
  {u | halfLineEdge (thresholdSiteEnvironment p u) n <
    halfLineEdge (thresholdSiteEnvironment q u) n}

/-- No strict split has occurred through this level, including the level itself. -/
def noEdgeSplitThrough (p q : unitInterval) (n : ℕ) : Set Environment :=
  {u | ∀ j ≤ n, u ∉ edgeSplit p q j}

/-- The first strict split is at the specified arrival level. -/
def firstEdgeSplitAt (p q : unitInterval) (n : ℕ) : Set Environment :=
  {u | u ∈ edgeSplit p q n ∧ ∀ j < n, u ∉ edgeSplit p q j}

/-- The threshold field uses the higher density through the first split, and the lower
density on every later arrival level. If no split occurs it keeps the higher density. -/
noncomputable def firstSplitContinuationEnvironment (p q : unitInterval)
    (u : Environment) : Environment := by
  classical
  exact fun z => if ∀ j : ℕ, (j : ℤ) < z.1 + z.2 → u ∉ edgeSplit p q j
    then thresholdSiteEnvironment q u z else thresholdSiteEnvironment p u z

/-- Thresholding preserves measurability with respect to any initial segment of levels. -/
theorem measurable_thresholdSiteEnvironment_levels (p : unitInterval) (m : ℤ) :
    @Measurable Environment Environment (levelsAtMost m) (levelsAtMost m)
      (thresholdSiteEnvironment p) := by
  rw [measurable_iff_comap_le]
  conv_lhs => unfold levelsAtMost
  simp_rw [MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  refine iSup₂_le fun z hz => ?_
  exact ((Measurable.ite measurableSet_Iic measurable_const measurable_const :
    Measurable (fun x : ℝ => if x ≤ (p : ℝ) then (1 : ℝ) else 0)).comp
    (measurable_site m hz)).comap_le

/-- A threshold half-line edge depends measurably on the uniforms through its arrival level. -/
theorem measurable_thresholdHalfLineEdge_levels (p : unitInterval) (n : ℕ) :
    Measurable[levelsAtMost (n : ℤ)] (fun u => halfLineEdge (thresholdSiteEnvironment p u) n) :=
  (measurable_halfLineEdge_levels n).comp (measurable_thresholdSiteEnvironment_levels p n)

/-- A split at this level is measurable from the uniforms through the level. -/
theorem measurableSet_edgeSplit_levels (p q : unitInterval) (n : ℕ) :
    MeasurableSet[levelsAtMost (n : ℤ)] (edgeSplit p q n) :=
  measurableSet_lt (measurable_thresholdHalfLineEdge_levels p n)
    (measurable_thresholdHalfLineEdge_levels q n)

/-- The event of no split through a level is measurable from those levels. -/
theorem measurableSet_noEdgeSplitThrough_levels (p q : unitInterval) (n : ℕ) :
    MeasurableSet[levelsAtMost (n : ℤ)] (noEdgeSplitThrough p q n) := by
  have h : noEdgeSplitThrough p q n = ⋂ j : {j : ℕ // j ≤ n}, (edgeSplit p q j)ᶜ := by
    ext u
    simp only [noEdgeSplitThrough, mem_ofPred_eq, mem_iInter, mem_compl_iff, Subtype.forall]
  rw [h]
  exact MeasurableSet.iInter fun j =>
    (levelsAtMost_mono (Int.ofNat_le.mpr j.2) _ (measurableSet_edgeSplit_levels p q j)).compl

/-- The first-split event at a level is measurable from the uniforms through that level. -/
theorem measurableSet_firstEdgeSplitAt_levels (p q : unitInterval) (n : ℕ) :
    MeasurableSet[levelsAtMost (n : ℤ)] (firstEdgeSplitAt p q n) := by
  have h : firstEdgeSplitAt p q n = edgeSplit p q n ∩
      ⋂ j : {j : ℕ // j < n}, (edgeSplit p q j)ᶜ := by
    ext u
    simp only [firstEdgeSplitAt, mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_compl_iff,
      Subtype.forall]
  rw [h]
  exact (measurableSet_edgeSplit_levels p q n).inter (MeasurableSet.iInter fun j =>
    (levelsAtMost_mono (Int.ofNat_le.mpr j.2.le) _ (measurableSet_edgeSplit_levels p q j)).compl)

/-- The first split has a unique level. -/
theorem firstEdgeSplitAt_unique {p q : unitInterval} {u : Environment} {m n : ℕ}
    (hm : u ∈ firstEdgeSplitAt p q m) (hn : u ∈ firstEdgeSplitAt p q n) : m = n := by
  apply le_antisymm
  · exact Nat.le_of_not_gt fun h => hm.2 n h hn.1
  · exact Nat.le_of_not_gt fun h => hn.2 m h hm.1

/-- A split has occurred through level `n` exactly when a first split has occurred by then. -/
theorem compl_noEdgeSplitThrough_eq_iUnion (p q : unitInterval) (n : ℕ) :
    (noEdgeSplitThrough p q n)ᶜ = ⋃ j : Fin (n + 1), firstEdgeSplitAt p q j := by
  classical
  ext u
  rw [mem_compl_iff, mem_iUnion]
  change (¬ ∀ j ≤ n, u ∉ edgeSplit p q j) ↔
    ∃ j : Fin (n + 1), u ∈ firstEdgeSplitAt p q j
  push Not
  constructor
  · rintro ⟨j, hjn, hj⟩
    have hex : ∃ k : ℕ, u ∈ edgeSplit p q k := ⟨j, hj⟩
    exact ⟨⟨Nat.find hex, Nat.lt_succ_of_le ((Nat.find_min' hex hj).trans hjn)⟩,
      Nat.find_spec hex, fun k hk => Nat.find_min hex hk⟩
  · rintro ⟨j, hj⟩
    exact ⟨j, Nat.le_of_lt_succ j.isLt, hj.1⟩

/-- At level zero the two fields start from the same half-line. -/
theorem noEdgeSplitThrough_zero (p q : unitInterval) : noEdgeSplitThrough p q 0 = univ := by
  ext u
  simp [noEdgeSplitThrough, edgeSplit, halfLineEdge_zero]

/-- The stopped continuation field is measurable in the common uniforms. -/
theorem measurable_firstSplitContinuationEnvironment (p q : unitInterval) :
    Measurable (firstSplitContinuationEnvironment p q) := by
  classical
  refine Measurable.of_eval fun z => ?_
  have hEvent : {u : Environment | ∀ j : ℕ, (j : ℤ) < z.1 + z.2 →
      u ∉ edgeSplit p q j} = ⋂ j : {j : ℕ // (j : ℤ) < z.1 + z.2}, (edgeSplit p q j)ᶜ := by
    ext u
    simp only [mem_ofPred_eq, mem_iInter, mem_compl_iff, Subtype.forall]
  refine Measurable.ite ?_ ((measurable_pi_apply z).comp
    (measurable_thresholdSiteEnvironment q)) ((measurable_pi_apply z).comp
    (measurable_thresholdSiteEnvironment p))
  rw [hEvent]
  exact MeasurableSet.iInter fun j =>
    (levelsAtMost_le _ _ (measurableSet_edgeSplit_levels p q j)).compl

/-- The continuation field agrees with the high-density field through the split. -/
theorem firstSplitContinuationEnvironment_eq_high {p q : unitInterval} {u : Environment}
    {n : ℕ} (h : u ∈ firstEdgeSplitAt p q n) {z : Lattice} (hz : z.1 + z.2 ≤ n) :
    firstSplitContinuationEnvironment p q u z = thresholdSiteEnvironment q u z := by
  classical
  unfold firstSplitContinuationEnvironment
  exact ite_eq_left fun j hj => h.2 j (by omega)

/-- Strictly after the first split, the continuation uses the low-density field. -/
theorem firstSplitContinuationEnvironment_eq_low {p q : unitInterval} {u : Environment}
    {n : ℕ} (h : u ∈ firstEdgeSplitAt p q n) {z : Lattice} (hz : (n : ℤ) < z.1 + z.2) :
    firstSplitContinuationEnvironment p q u z = thresholdSiteEnvironment p u z := by
  classical
  unfold firstSplitContinuationEnvironment
  exact ite_eq_right fun h' => h' n hz h.1

/-- The two threshold fields bound the continuation field in open sites. -/
theorem firstSplitContinuation_topSites_bounds {p q : unitInterval} (hpq : p ≤ q)
    (u : Environment) :
    topSites (thresholdSiteEnvironment p u) ⊆ topSites (firstSplitContinuationEnvironment p q u) ∧
    topSites (firstSplitContinuationEnvironment p q u) ⊆ topSites (thresholdSiteEnvironment q u) := by
  classical
  have h := topSites_thresholdSiteEnvironment_mono u hpq
  constructor <;> intro z hz
  · change firstSplitContinuationEnvironment p q u z = 1
    unfold firstSplitContinuationEnvironment
    split
    · exact h hz
    · exact hz
  · change firstSplitContinuationEnvironment p q u z = 1 at hz
    unfold firstSplitContinuationEnvironment at hz
    split at hz
    · exact hz
    · exact h hz

/-- The Bernoulli law of any positive threshold has positive mass at the open weight. -/
theorem bernoulli_singleton_one_pos (p : unitInterval) (hp : 0 < (p : ℝ)) :
    0 < bernoulliMeasure (1 : ℝ) 0 p {1} := by
  rw [bernoulliMeasure_apply_of_mem_of_notMem p (measurableSet_singleton _) (by simp) (by simp),
    ENNReal.coe_nnreal_eq, unitInterval.coe_toNNReal]
  exact ENNReal.ofReal_pos.mpr hp

/-- At a positive threshold the half-line process reaches every level almost surely. -/
theorem ae_thresholdHalfLine_nonempty (p : unitInterval) (hp : 0 < (p : ℝ)) :
    ∀ᵐ u ∂siteUniformLaw, ∀ n : ℕ,
      (openReachSet (topSites (thresholdSiteEnvironment p u)) antidiagHalfLine n).Nonempty := by
  have h := (ae_openReachSet_halfLine_infinite _ (bernoulli_singleton_one_pos p hp)).mono
    (fun ω hω n => (hω n).nonempty)
  exact ae_of_ae_map (measurable_thresholdSiteEnvironment p).aemeasurable
    (by rwa [map_siteUniformLaw_thresholdSiteEnvironment])

end LPPDifferentiability.FinalDraft
