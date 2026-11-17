/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Geometry.CoalescingTiltTimeIndex
public import ProbabilityBasics.Analysis.CountableSidedSampleSet

@[expose] public section

open MeasureTheory Filter LPPDifferentiability
open scoped ENNReal Topology

namespace LPP.Busemann

/-- A single countable set of coalescing tilts samples both strict first-coordinate
sides of every tilt outside the set. The time-index construction uses the tilt order and one-sided limits. -/
theorem exists_countable_sided_sample_coalescingTilts
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.NotAPointMass μ)
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞) :
    ∃ D : Set (CoalescingTilt μ), D.Countable ∧
      ∀ h : CoalescingTilt μ, h ∉ D →
        h ∈ closure (D ∩ {k | k.val.1 < h.val.1}) ∧
        h ∈ closure (D ∩ {k | h.val.1 < k.val.1}) := by
  classical
  -- Choose the two-sided sample on the actual scalar-time subtype.
  obtain ⟨timeSamples, htimeSamplesCountable, htimeSamplesBoth⟩ :=
    ProbabilityBasics.exists_countable_sided_sample_set (timeSet μ)

  -- Keep the topology and strict first-coordinate order on the actual H subtype.
  have hTimeIndexEmbedding : Topology.IsEmbedding (timeIndex μ) :=
    timeIndex_isEmbedding μ hμ hmoment

  -- Pull the one actual-time exceptional set back to the tilt carrier.
  let D : Set (CoalescingTilt μ) := (timeIndex μ) ⁻¹' timeSamples
  have hDCountable : D.Countable := by
    simpa only [D] using
      htimeSamplesCountable.preimage (f := timeIndex μ) hTimeIndexEmbedding.injective

  -- Every point of the actual time set has a tilt preimage by definition.
  have hTimeIndexSurjective : Function.Surjective (timeIndex μ) := by
    intro t
    have htTime : ∃ k : CoalescingTilt μ, t.val = k.val.1 - k.val.2 := by
      change t.val ∈ timeSet μ
      exact t.property
    obtain ⟨k, hkTime⟩ := htTime
    refine ⟨k, ?_⟩
    apply Subtype.ext
    exact hkTime.symm

  refine ⟨D, hDCountable, ?_⟩
  intro h hhNotD

  -- An omitted tilt maps to an omitted actual time, so the generic lemma applies.
  have hTimeNotSamples : timeIndex μ h ∉ timeSamples := by
    intro hhTimeSamples
    apply hhNotD
    change timeIndex μ h ∈ timeSamples
    exact hhTimeSamples
  obtain ⟨hLeftTimeClosure, hRightTimeClosure⟩ :=
    htimeSamplesBoth (timeIndex μ h) hTimeNotSamples

  -- The image of the left tilt-side samples is exactly the left actual-time samples.
  have hLeftImage :
      timeIndex μ '' (D ∩ {k : CoalescingTilt μ | k.val.1 < h.val.1}) =
        timeSamples ∩ Set.Iio (timeIndex μ h) := by
    ext t
    constructor
    · rintro ⟨k, ⟨hkD, hkLeft⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · change timeIndex μ k ∈ timeSamples
        exact hkD
      · change (timeIndex μ k).val < (timeIndex μ h).val
        exact (timeIndex_lt_iff_first_coordinate_lt μ hμ hmoment k h).2 hkLeft
    · rintro ⟨htSamples, htLeft⟩
      obtain ⟨k, hkTime⟩ := hTimeIndexSurjective t
      have hkD : k ∈ D := by
        change timeIndex μ k ∈ timeSamples
        rw [hkTime]
        exact htSamples
      have hkLeft : k.val.1 < h.val.1 := by
        have hkTimeLeft : timeIndex μ k < timeIndex μ h := by
          rw [hkTime]
          exact htLeft
        exact (timeIndex_lt_iff_first_coordinate_lt μ hμ hmoment k h).1
          (by simpa using hkTimeLeft)
      exact ⟨k, ⟨hkD, hkLeft⟩, hkTime⟩

  -- The image of the right tilt-side samples is exactly the right actual-time samples.
  have hRightImage :
      timeIndex μ '' (D ∩ {k : CoalescingTilt μ | h.val.1 < k.val.1}) =
        timeSamples ∩ Set.Ioi (timeIndex μ h) := by
    ext t
    constructor
    · rintro ⟨k, ⟨hkD, hkRight⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · change timeIndex μ k ∈ timeSamples
        exact hkD
      · change (timeIndex μ h).val < (timeIndex μ k).val
        exact (timeIndex_lt_iff_first_coordinate_lt μ hμ hmoment h k).2 hkRight
    · rintro ⟨htSamples, htRight⟩
      obtain ⟨k, hkTime⟩ := hTimeIndexSurjective t
      have hkD : k ∈ D := by
        change timeIndex μ k ∈ timeSamples
        rw [hkTime]
        exact htSamples
      have hkRight : h.val.1 < k.val.1 := by
        have hkTimeRight : timeIndex μ h < timeIndex μ k := by
          rw [hkTime]
          exact htRight
        exact (timeIndex_lt_iff_first_coordinate_lt μ hμ hmoment h k).1
          (by simpa using hkTimeRight)
      exact ⟨k, ⟨hkD, hkRight⟩, hkTime⟩

  -- The embedding transfers each actual-time closure to the actual tilt topology.
  have hLeftClosure :
      h ∈ closure (D ∩ {k : CoalescingTilt μ | k.val.1 < h.val.1}) := by
    rw [hTimeIndexEmbedding.closure_eq_preimage_closure_image]
    change timeIndex μ h ∈
      closure (timeIndex μ '' (D ∩ {k : CoalescingTilt μ | k.val.1 < h.val.1}))
    rw [hLeftImage]
    exact hLeftTimeClosure
  have hRightClosure :
      h ∈ closure (D ∩ {k : CoalescingTilt μ | h.val.1 < k.val.1}) := by
    rw [hTimeIndexEmbedding.closure_eq_preimage_closure_image]
    change timeIndex μ h ∈
      closure (timeIndex μ '' (D ∩ {k : CoalescingTilt μ | h.val.1 < k.val.1}))
    rw [hRightImage]
    exact hRightTimeClosure

  exact ⟨hLeftClosure, hRightClosure⟩

end LPP.Busemann
