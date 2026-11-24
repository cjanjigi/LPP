/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.FlatDensitySource.SplitProbability
public import Differentiability.Probability.RightBlockGain
import all Differentiability.Probability.RightBlockGain
import all Differentiability.FinalDraft.FlatTopRates.RightContinuity
import Differentiability.Model.OrientedPercolationLaws

/-! The pathwise comparison behind Durrett's right-block gain after the first split. -/

@[expose] public section

open MeasureTheory Set

namespace LPPDifferentiability.FinalDraft

/-- The site immediately left of the high edge, on the same level as the split. -/
noncomputable def firstSplitCenter (q : unitInterval) (m : ℕ) (u : Environment) : Lattice :=
  thresholdEdgeSite q m u - (1, -1)

/-- The center of the continuation lies on the split level. -/
theorem firstSplitCenter_level (q : unitInterval) (m : ℕ) (u : Environment) :
    (firstSplitCenter q m u).1 + (firstSplitCenter q m u).2 = (m : ℤ) := by
  have h := thresholdEdgeSite_level q m u
  simp only [firstSplitCenter, Prod.fst_sub, Prod.snd_sub]
  omega

/-- The center is measurable using the uniforms through the split level. -/
theorem measurable_firstSplitCenter_levels (q : unitInterval) (m : ℕ) :
    Measurable[levelsAtMost (m : ℤ)] (firstSplitCenter q m) :=
  (Measurable.of_discrete (f := fun z : Lattice => z - (1, -1))).comp
    (measurable_thresholdEdgeSite_levels q m)

/-- Gain from adding the first site to the right of a whole half-line, in the fixed field. -/
noncomputable def halfLineOneSiteGain (ω : Environment) (n : ℕ) : ℝ :=
  (openEdge (topSites ω) (antidiagHalfLine ∪ antidiagRightBlock 1) n : ℝ) -
    halfLineEdge ω n

/-- The one-site block consists of the relative point (1,-1). -/
private theorem antidiagRightBlock_one : antidiagRightBlock 1 = {(1, -1)} := by
  ext z
  change (z.1 + z.2 = 0 ∧ 1 ≤ z.1 ∧ z.1 ≤ ((1 : ℕ) : ℤ)) ↔ z = ((1, -1) : Lattice)
  rw [Prod.ext_iff]
  change (z.1 + z.2 = 0 ∧ 1 ≤ z.1 ∧ z.1 ≤ 1) ↔ z.1 = 1 ∧ z.2 = -1
  omega

/-- Through the split, the stopped continuation has the same reached set as the higher field. -/
private theorem firstSplitContinuation_reach_at {p q : unitInterval} {u : Environment}
    {m : ℕ} (hm : u ∈ firstEdgeSplitAt p q m) :
    openReachSet (topSites (firstSplitContinuationEnvironment p q u)) antidiagHalfLine m =
      openReachSet (topSites (thresholdSiteEnvironment q u)) antidiagHalfLine m := by
  refine openReachSet_congr _ _ _ 0 m antidiagHalfLine_subset_levelSet (fun z _ hz => ?_)
  show firstSplitContinuationEnvironment p q u z = 1 ↔ thresholdSiteEnvironment q u z = 1
  rw [firstSplitContinuationEnvironment_eq_high hm (by simpa only [zero_add] using hz)]

/-- After a split, restart from the higher reached set and read the lower field. -/
private theorem firstSplitContinuation_reach_add {p q : unitInterval} {u : Environment}
    {m : ℕ} (hm : u ∈ firstEdgeSplitAt p q m) (k : ℕ) :
    openReachSet (topSites (firstSplitContinuationEnvironment p q u)) antidiagHalfLine (m + k) =
      openReachSet (topSites (thresholdSiteEnvironment p u))
        (openReachSet (topSites (thresholdSiteEnvironment q u)) antidiagHalfLine m) k := by
  rw [← openReachSet_add, firstSplitContinuation_reach_at hm]
  have hs : openReachSet (topSites (thresholdSiteEnvironment q u)) antidiagHalfLine m ⊆
      levelSet (m : ℤ) := by
    simpa only [zero_add] using openReachSet_subset_levelSet _ _ 0 m antidiagHalfLine_subset_levelSet
  refine openReachSet_congr _ _ _ (m : ℤ) k hs (fun z hz _ => ?_)
  show firstSplitContinuationEnvironment p q u z = 1 ↔ thresholdSiteEnvironment p u z = 1
  rw [firstSplitContinuationEnvironment_eq_low hm hz]

/-- On the first-split fiber, the stopped continuation gains at least the one-site gain
of the ordinary half-line in the translated future. This is the site version of Durrett's
comparison (13). -/
theorem halfLineOneSiteGain_le_firstSplitContinuation_gap {p q : unitInterval}
    (hpq : p ≤ q) {u : Environment} {m : ℕ} (hm : u ∈ firstEdgeSplitAt p q m)
    (k : ℕ)
    (hne : ∀ j, (openReachSet (topSites (thresholdSiteEnvironment p u))
      antidiagHalfLine j).Nonempty) :
    halfLineOneSiteGain
        (thresholdSiteEnvironment p (fun z => u (firstSplitCenter q m u + z))) k ≤
      (halfLineEdge (firstSplitContinuationEnvironment p q u) (m + k) : ℝ) -
        halfLineEdge (thresholdSiteEnvironment p u) (m + k) := by
  let ω := thresholdSiteEnvironment p u
  let η := thresholdSiteEnvironment q u
  let T := firstSplitCenter q m u
  let L := openReachSet (topSites ω) antidiagHalfLine m
  let Q := openReachSet (topSites η) antidiagHalfLine m
  let B := (fun z : Lattice => T + z) ⁻¹' L
  let F := antidiagRightBlock 1
  let O := topSites (fun z => ω (T + z))
  have hLQ : L ⊆ Q :=
    openReachSet_mono (topSites_thresholdSiteEnvironment_mono u hpq) subset_rfl m
  have hB : B ⊆ antidiagHalfLine := by
    intro z h
    have hz : T + z ∈ L := h
    have hlevel : (T + z).1 + (T + z).2 = (m : ℤ) := by
      have := openReachSet_subset_levelSet _ _ 0 m antidiagHalfLine_subset_levelSet hz
      simpa [levelSet] using this
    have hT : T.1 + T.2 = (m : ℤ) := firstSplitCenter_level q m u
    have hbound := le_maxFirst _ (bddAbove_fst_halfLineReach ω m) hz
    change (T + z).1 ≤ halfLineEdge ω m at hbound
    have hsplit : halfLineEdge ω m < halfLineEdge η m := hm.1
    have hfst : T.1 = halfLineEdge η m - 1 := rfl
    simp only [Prod.fst_add, Prod.snd_add] at hbound hlevel
    exact ⟨by omega, by omega⟩
  have hBimage : (fun z => T + z) '' B = L := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hz
      exact ⟨-T + z, by change T + (-T + z) ∈ L; rwa [add_neg_cancel_left],
        add_neg_cancel_left T z⟩
  have hFQ : (fun z => T + z) '' F ⊆ Q := by
    rintro _ ⟨z, hz, rfl⟩
    have hFz : z = ((1, -1) : Lattice) := by
      rwa [show F = {(1, -1)} by exact antidiagRightBlock_one, mem_singleton_iff] at hz
    change T + z ∈ Q
    rw [hFz, show T + (1, -1) = thresholdEdgeSite q m u from sub_add_cancel _ _]
    exact thresholdEdgeSite_mem ((hne m).mono hLQ)
  have haugQ : (fun z => T + z) '' (B ∪ F) ⊆ Q := by
    rw [Set.image_union, hBimage]
    exact union_subset hLQ hFQ
  have hbdB : BddAbove (Prod.fst '' B) :=
    bddAbove_fst_antidiagHalfLine.mono (image_mono hB)
  have hbdF : BddAbove (Prod.fst '' F) := bddAbove_fst_antidiagRightBlock 1
  have hneL : (openReachSet (topSites ω) L k).Nonempty := by
    simpa only [L, openReachSet_add] using hne (m + k)
  have hneBImage : (openReachSet (topSites ω) ((fun z => T + z) '' B) k).Nonempty :=
    hBimage ▸ hneL
  have hneB : (openReachSet O B k).Nonempty := by
    obtain ⟨z, hz⟩ := hneBImage
    refine ⟨-T + z, ?_⟩
    change -T + z ∈ openReachSet ((fun w : Lattice => T + w) ⁻¹' topSites ω) B k
    apply (mem_openReachSet_translate (topSites ω) B T (-T + z) k).2
    simpa only [add_neg_cancel_left] using hz
  have hneAug : (openReachSet (topSites ω) ((fun z => T + z) '' (B ∪ F)) k).Nonempty :=
    hneBImage.mono (openReachSet_mono subset_rfl (image_mono subset_union_left) k)
  have hlo := openEdge_translate ω B T k hneBImage hbdB
  rw [hBimage] at hlo
  have hag := openEdge_translate ω (B ∪ F) T k hneAug (bddAbove_fst_union hbdB hbdF)
  have htoQ : openEdge (topSites ω) ((fun z => T + z) '' (B ∪ F)) k ≤
      openEdge (topSites ω) Q k := by
    have hbdQ := bddAbove_fst_reach (topSites ω) k (bddAbove_fst_halfLineReach η m)
    unfold openEdge
    exact csSup_le_csSup hbdQ (hneAug.image Prod.fst)
      (image_mono (openReachSet_mono subset_rfl haugQ k))
  have hcmp := openEdge_union_gain_antitone O B antidiagHalfLine F k hB hneB
    bddAbove_fst_antidiagHalfLine hbdF
  change openEdge O (antidiagHalfLine ∪ F) k - openEdge O antidiagHalfLine k ≤ _ at hcmp
  have hleft : openEdge (topSites ω) L k = halfLineEdge ω (m + k) := by
    change maxFirst (openReachSet (topSites ω) L k) =
      maxFirst (openReachSet (topSites ω) antidiagHalfLine (m + k))
    rw [show L = openReachSet (topSites ω) antidiagHalfLine m from rfl, openReachSet_add]
  have hright : openEdge (topSites ω) Q k =
      halfLineEdge (firstSplitContinuationEnvironment p q u) (m + k) := by
    change maxFirst (openReachSet (topSites ω) Q k) =
      maxFirst (openReachSet (topSites (firstSplitContinuationEnvironment p q u))
        antidiagHalfLine (m + k))
    rw [firstSplitContinuation_reach_add hm]
  have hg : openEdge O (antidiagHalfLine ∪ F) k - openEdge O antidiagHalfLine k ≤
      halfLineEdge (firstSplitContinuationEnvironment p q u) (m + k) -
        halfLineEdge ω (m + k) := by
    change openEdge (topSites ω) L k = T.1 + openEdge O B k at hlo
    change openEdge (topSites ω) ((fun z => T + z) '' (B ∪ F)) k =
      T.1 + openEdge O (B ∪ F) k at hag
    rw [hleft] at hlo
    rw [hag, hright] at htoQ
    omega
  unfold halfLineOneSiteGain
  exact_mod_cast hg

end LPPDifferentiability.FinalDraft
