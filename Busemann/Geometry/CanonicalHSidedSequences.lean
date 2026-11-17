/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Geometry.CoalescingTiltSidedSample
public import Mathlib.Topology.Order.IsLUB

@[expose] public section

open MeasureTheory Filter LPPDifferentiability
open scoped ENNReal Topology

namespace LPP.Busemann

/-- Every omitted tilt is the limit of strict sampled approximants from both
first-coordinate sides; sampled tilts use constant sequences. This is the
sequence step for *Strong Existence*, lines 1194–1217. -/
theorem exists_canonical_H_sample_sided_sequences
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.NotAPointMass μ)
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    (D : Set (CoalescingTilt μ))
    (hSides : ∀ h : CoalescingTilt μ, h ∉ D →
      h ∈ closure (D ∩ {k | k.val.1 < h.val.1}) ∧
      h ∈ closure (D ∩ {k | h.val.1 < k.val.1})) :
    ∃ left right : CoalescingTilt μ → ℕ → CoalescingTilt μ,
      ∀ h : CoalescingTilt μ,
        (h ∈ D → left h = (fun _ => h) ∧ right h = (fun _ => h)) ∧
        (h ∉ D →
          (∀ n, left h n ∈ D ∧ (left h n).val.1 < h.val.1) ∧
          StrictMono (fun n => (left h n).val.1) ∧
          Tendsto (left h) atTop (𝓝 h) ∧
          (∀ n, right h n ∈ D ∧ h.val.1 < (right h n).val.1) ∧
          StrictAnti (fun n => (right h n).val.1) ∧
          Tendsto (right h) atTop (𝓝 h)) := by
  classical

  -- The actual time index retains both the H topology and its strict order.
  have hTimeIndexEmbedding : Topology.IsEmbedding (timeIndex μ) :=
    timeIndex_isEmbedding μ hμ hmoment
  let TimeSubtype := {t : ℝ // t ∈ timeSet μ}
  have hTimeValueEmbedding : Topology.IsEmbedding
      (fun t : TimeSubtype => (t : ℝ)) := Topology.IsEmbedding.subtypeVal

  -- For an omitted tilt, find real-time sequences from the two closure sides.
  have hOmittedSequences (h : CoalescingTilt μ) (hhNotD : h ∉ D) :
      ∃ leftSeq rightSeq : ℕ → CoalescingTilt μ,
        (∀ n, leftSeq n ∈ D ∧ (leftSeq n).val.1 < h.val.1) ∧
        StrictMono (fun n => (leftSeq n).val.1) ∧
        Tendsto leftSeq atTop (𝓝 h) ∧
        (∀ n, rightSeq n ∈ D ∧ h.val.1 < (rightSeq n).val.1) ∧
        StrictAnti (fun n => (rightSeq n).val.1) ∧
        Tendsto rightSeq atTop (𝓝 h) := by
    let leftTilts := D ∩ {k : CoalescingTilt μ | k.val.1 < h.val.1}
    let rightTilts := D ∩ {k : CoalescingTilt μ | h.val.1 < k.val.1}
    let leftTimes : Set ℝ :=
      (fun t : TimeSubtype => (t : ℝ)) '' (timeIndex μ '' leftTilts)
    let rightTimes : Set ℝ :=
      (fun t : TimeSubtype => (t : ℝ)) '' (timeIndex μ '' rightTilts)
    let targetTime : ℝ := (timeIndex μ h).val

    -- Move both H-side closures through the actual-time embedding and subtype value.
    have hLeftTiltClosure : h ∈ closure leftTilts := by
      simpa only [leftTilts] using (hSides h hhNotD).1
    have hRightTiltClosure : h ∈ closure rightTilts := by
      simpa only [rightTilts] using (hSides h hhNotD).2
    have hLeftTimeClosure :
        timeIndex μ h ∈ closure (timeIndex μ '' leftTilts) := by
      have hClosureEq :=
        hTimeIndexEmbedding.closure_eq_preimage_closure_image leftTilts
      simpa only [hClosureEq, Set.mem_preimage] using hLeftTiltClosure
    have hRightTimeClosure :
        timeIndex μ h ∈ closure (timeIndex μ '' rightTilts) := by
      have hClosureEq :=
        hTimeIndexEmbedding.closure_eq_preimage_closure_image rightTilts
      simpa only [hClosureEq, Set.mem_preimage] using hRightTiltClosure
    have hLeftScalarClosure : targetTime ∈ closure leftTimes := by
      have hClosureEq :=
        hTimeValueEmbedding.closure_eq_preimage_closure_image
          (timeIndex μ '' leftTilts)
      simpa only [leftTimes, targetTime, hClosureEq, Set.mem_preimage]
        using hLeftTimeClosure
    have hRightScalarClosure : targetTime ∈ closure rightTimes := by
      have hClosureEq :=
        hTimeValueEmbedding.closure_eq_preimage_closure_image
          (timeIndex μ '' rightTilts)
      simpa only [rightTimes, targetTime, hClosureEq, Set.mem_preimage]
        using hRightTimeClosure

    -- Every real sample lies strictly on its prescribed side of the target time.
    have hLeftUpper : targetTime ∈ upperBounds leftTimes := by
      intro x hx
      change x ∈ (fun t : TimeSubtype => (t : ℝ)) ''
        (timeIndex μ '' leftTilts) at hx
      rcases hx with ⟨t, ht, htx⟩
      rcases ht with ⟨k, hk, hkt⟩
      have hValue : (timeIndex μ k).val = x := by
        calc
          (timeIndex μ k).val = (t : ℝ) := congrArg Subtype.val hkt
          _ = x := htx
      rw [← hValue]
      exact le_of_lt
        ((timeIndex_lt_iff_first_coordinate_lt μ hμ hmoment k h).2 hk.2)
    have hRightLower : targetTime ∈ lowerBounds rightTimes := by
      intro x hx
      change x ∈ (fun t : TimeSubtype => (t : ℝ)) ''
        (timeIndex μ '' rightTilts) at hx
      rcases hx with ⟨t, ht, htx⟩
      rcases ht with ⟨k, hk, hkt⟩
      have hValue : (timeIndex μ k).val = x := by
        calc
          (timeIndex μ k).val = (t : ℝ) := congrArg Subtype.val hkt
          _ = x := htx
      rw [← hValue]
      exact le_of_lt
        ((timeIndex_lt_iff_first_coordinate_lt μ hμ hmoment h k).2 hk.2)

    -- The strict side conditions ensure the target is not itself a sample.
    have hLeftNotMem : targetTime ∉ leftTimes := by
      intro hx
      change targetTime ∈ (fun t : TimeSubtype => (t : ℝ)) ''
        (timeIndex μ '' leftTilts) at hx
      rcases hx with ⟨t, ht, htx⟩
      rcases ht with ⟨k, hk, hkt⟩
      have hValue : (timeIndex μ k).val = targetTime := by
        calc
          (timeIndex μ k).val = (t : ℝ) := congrArg Subtype.val hkt
          _ = targetTime := htx
      have hlt :=
        (timeIndex_lt_iff_first_coordinate_lt μ hμ hmoment k h).2 hk.2
      rw [hValue] at hlt
      exact (lt_irrefl targetTime hlt).elim
    have hRightNotMem : targetTime ∉ rightTimes := by
      intro hx
      change targetTime ∈ (fun t : TimeSubtype => (t : ℝ)) ''
        (timeIndex μ '' rightTilts) at hx
      rcases hx with ⟨t, ht, htx⟩
      rcases ht with ⟨k, hk, hkt⟩
      have hValue : (timeIndex μ k).val = targetTime := by
        calc
          (timeIndex μ k).val = (t : ℝ) := congrArg Subtype.val hkt
          _ = targetTime := htx
      have hlt :=
        (timeIndex_lt_iff_first_coordinate_lt μ hμ hmoment h k).2 hk.2
      rw [hValue] at hlt
      exact (lt_irrefl targetTime hlt).elim

    -- Closure supplies nonempty sets, so the real least/greatest bounds yield strict sequences.
    have hLeftNonempty : leftTimes.Nonempty := by
      by_contra hEmpty
      have hEmptySet : leftTimes = ∅ := Set.not_nonempty_iff_eq_empty.mp hEmpty
      simp [hEmptySet] at hLeftScalarClosure
    have hRightNonempty : rightTimes.Nonempty := by
      by_contra hEmpty
      have hEmptySet : rightTimes = ∅ := Set.not_nonempty_iff_eq_empty.mp hEmpty
      simp [hEmptySet] at hRightScalarClosure
    have hLeftIsLUB : IsLUB leftTimes targetTime :=
      isLUB_of_mem_closure hLeftUpper hLeftScalarClosure
    have hRightIsGLB : IsGLB rightTimes targetTime :=
      isGLB_of_mem_closure hRightLower hRightScalarClosure
    obtain ⟨leftTimeSeq, hLeftTimeStrict, _, hLeftTimeTendsto,
      hLeftTimeMem⟩ :=
      hLeftIsLUB.exists_seq_strictMono_tendsto_of_notMem
        hLeftNotMem hLeftNonempty
    obtain ⟨rightTimeSeq, hRightTimeStrict, _, hRightTimeTendsto,
      hRightTimeMem⟩ :=
      hRightIsGLB.exists_seq_strictAnti_tendsto_of_notMem
        hRightNotMem hRightNonempty

    -- Pull each real sample back to a tilt in D using its image membership.
    have hLeftPreimage (n : ℕ) :
        ∃ k : CoalescingTilt μ, k ∈ leftTilts ∧
          (timeIndex μ k).val = leftTimeSeq n := by
      have hMem : leftTimeSeq n ∈ leftTimes := hLeftTimeMem n
      change leftTimeSeq n ∈ (fun t : TimeSubtype => (t : ℝ)) ''
        (timeIndex μ '' leftTilts) at hMem
      rcases hMem with ⟨t, ht, htn⟩
      rcases ht with ⟨k, hk, hkt⟩
      refine ⟨k, hk, ?_⟩
      calc
        (timeIndex μ k).val = (t : ℝ) := congrArg Subtype.val hkt
        _ = leftTimeSeq n := htn
    have hRightPreimage (n : ℕ) :
        ∃ k : CoalescingTilt μ, k ∈ rightTilts ∧
          (timeIndex μ k).val = rightTimeSeq n := by
      have hMem : rightTimeSeq n ∈ rightTimes := hRightTimeMem n
      change rightTimeSeq n ∈ (fun t : TimeSubtype => (t : ℝ)) ''
        (timeIndex μ '' rightTilts) at hMem
      rcases hMem with ⟨t, ht, htn⟩
      rcases ht with ⟨k, hk, hkt⟩
      refine ⟨k, hk, ?_⟩
      calc
        (timeIndex μ k).val = (t : ℝ) := congrArg Subtype.val hkt
        _ = rightTimeSeq n := htn
    choose leftSeq hLeftSeq using hLeftPreimage
    choose rightSeq hRightSeq using hRightPreimage

    -- The time order transfers strictness to the first tilt coordinate.
    have hLeftFirstStrict : StrictMono (fun n => (leftSeq n).val.1) := by
      intro n m hnm
      have hTime : (timeIndex μ (leftSeq n)).val <
          (timeIndex μ (leftSeq m)).val := by
        rw [(hLeftSeq n).2, (hLeftSeq m).2]
        exact hLeftTimeStrict hnm
      exact (timeIndex_lt_iff_first_coordinate_lt μ hμ hmoment
        (leftSeq n) (leftSeq m)).1 hTime
    have hRightFirstStrict : StrictAnti (fun n => (rightSeq n).val.1) := by
      intro n m hnm
      have hTime : (timeIndex μ (rightSeq m)).val <
          (timeIndex μ (rightSeq n)).val := by
        rw [(hRightSeq m).2, (hRightSeq n).2]
        exact hRightTimeStrict hnm
      exact (timeIndex_lt_iff_first_coordinate_lt μ hμ hmoment
        (rightSeq m) (rightSeq n)).1 hTime

    -- Lift scalar convergence twice, first into actual time and then into H.
    have hLeftScalarTendsto :
        Tendsto (fun n => (timeIndex μ (leftSeq n)).val) atTop
          (𝓝 targetTime) := by
      have hValues :
          (fun n => (timeIndex μ (leftSeq n)).val) = leftTimeSeq := by
        funext n
        exact (hLeftSeq n).2
      rw [hValues]
      exact hLeftTimeTendsto
    have hRightScalarTendsto :
        Tendsto (fun n => (timeIndex μ (rightSeq n)).val) atTop
          (𝓝 targetTime) := by
      have hValues :
          (fun n => (timeIndex μ (rightSeq n)).val) = rightTimeSeq := by
        funext n
        exact (hRightSeq n).2
      rw [hValues]
      exact hRightTimeTendsto
    have hLeftActualTimeTendsto :
        Tendsto (fun n => timeIndex μ (leftSeq n)) atTop
          (𝓝 (timeIndex μ h)) :=
      hTimeValueEmbedding.tendsto_nhds_iff.mpr hLeftScalarTendsto
    have hRightActualTimeTendsto :
        Tendsto (fun n => timeIndex μ (rightSeq n)) atTop
          (𝓝 (timeIndex μ h)) :=
      hTimeValueEmbedding.tendsto_nhds_iff.mpr hRightScalarTendsto
    have hLeftHTendsto : Tendsto leftSeq atTop (𝓝 h) :=
      hTimeIndexEmbedding.tendsto_nhds_iff.mpr hLeftActualTimeTendsto
    have hRightHTendsto : Tendsto rightSeq atTop (𝓝 h) :=
      hTimeIndexEmbedding.tendsto_nhds_iff.mpr hRightActualTimeTendsto

    refine ⟨leftSeq, rightSeq, ?_, hLeftFirstStrict, hLeftHTendsto,
      ?_, hRightFirstStrict, hRightHTendsto⟩
    · intro n
      exact ⟨(hLeftSeq n).1.1, (hLeftSeq n).1.2⟩
    · intro n
      exact ⟨(hRightSeq n).1.1, (hRightSeq n).1.2⟩

  -- Assemble the pointwise choices into the two required total sequence maps.
  have hPointwise (h : CoalescingTilt μ) :
      ∃ leftSeq rightSeq : ℕ → CoalescingTilt μ,
        (h ∈ D → leftSeq = (fun _ => h) ∧ rightSeq = (fun _ => h)) ∧
        (h ∉ D →
          (∀ n, leftSeq n ∈ D ∧ (leftSeq n).val.1 < h.val.1) ∧
          StrictMono (fun n => (leftSeq n).val.1) ∧
          Tendsto leftSeq atTop (𝓝 h) ∧
          (∀ n, rightSeq n ∈ D ∧ h.val.1 < (rightSeq n).val.1) ∧
          StrictAnti (fun n => (rightSeq n).val.1) ∧
          Tendsto rightSeq atTop (𝓝 h)) := by
    by_cases hD : h ∈ D
    · refine ⟨fun _ => h, fun _ => h, ?_, ?_⟩
      · intro _
        exact ⟨rfl, rfl⟩
      · intro hNotD
        exact (hNotD hD).elim
    · obtain ⟨leftSeq, rightSeq, hProperties⟩ := hOmittedSequences h hD
      refine ⟨leftSeq, rightSeq, ?_, ?_⟩
      · intro hInD
        exact (hD hInD).elim
      · intro _
        exact hProperties
  choose left right hProperties using hPointwise
  exact ⟨left, right, hProperties⟩

end LPP.Busemann
