/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.StrongExistence.Definitions.OneSidedLimits
public import Busemann.Frozen.Definitions.InvariantCocycleTilt

import Busemann.Process.CanonicalHFieldSelection
import Busemann.Geometry.CoalescingTiltSidedSample
import Busemann.Geometry.CanonicalHSidedSequences
import Busemann.Process.CanonicalHRawEnvelopes
import Busemann.Probability.CanonicalCocycleMeans
import Busemann.Process.CanonicalHRawFixedTilt
import Busemann.Process.CanonicalHRawSidedContinuity
import Busemann.Process.CanonicalHRawOrder

@[expose] public section
open MeasureTheory Filter LPPDifferentiability
open scoped ENNReal Topology
namespace LPP.Busemann

/-- The canonical forward fields and the same literal raw limit pair satisfy
all six source properties. Strong Existence, public lines 1194–1221. -/
theorem exists_strong_coupled_fields_of_absolute_moment
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.NotAPointMass μ)
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞) :
    ∃ Bm Bp : StrongField μ,
      BranchAgreement μ Bm Bp ∧ ForwardCoalescingClass μ Bm Bp ∧
      MeanTilt μ Bm ∧ WithinTiltOrder μ Bm Bp ∧
      StrictCrossTiltOrder μ Bm Bp ∧ OneSidedLimits μ Bm Bp := by
  classical
  -- Select one canonical field family with its full invariant tilt at every h.
  obtain ⟨C, hSelected⟩ :=
    exists_forward_canonical_field_on_coalescingTilts μ hμ hmoment
  have hClass : ForwardCoalescingClass μ C C := by
    intro h
    obtain ⟨hGen, hCoal, hForward, _⟩ := hSelected h
    exact ⟨hGen.1.1, hGen, hCoal, hForward⟩
  have hMean : MeanTilt μ C := by
    intro h
    obtain ⟨hGen, _, _, hTilt⟩ := hSelected h
    exact canonical_origin_means_of_deterministic_invariant_tilt
      μ (C h) hGen h.val hTilt

  -- Use one countable sample and one pair of strict sided sequences.
  obtain ⟨D, hD, hSides⟩ :=
    exists_countable_sided_sample_coalescingTilts μ hμ hmoment
  obtain ⟨left, right, hSequences⟩ :=
    exists_canonical_H_sample_sided_sequences μ hμ hmoment D hSides
  have hConstant : ∀ h : CoalescingTilt μ, h ∈ D →
      left h = (fun _ => h) ∧ right h = (fun _ => h) := by
    intro h hh
    exact (hSequences h).1 hh

  -- Produce the literal raw pair once and keep those witnesses for every clause.
  obtain ⟨Bm, Bp, hRaw, _, _⟩ :=
    exists_canonical_H_raw_sided_fields μ C hClass D left right hConstant
  have hFixed := canonical_H_raw_fields_fixed_tilt_class_and_mean
    μ hμ hmoment C hClass hMean D left right hSequences Bm Bp hRaw
  have hRawOrder := canonical_H_raw_fields_within_and_strict_cross_order
    μ hμ hmoment C hClass hMean D hD left right hSequences Bm Bp hRaw
  have hLimits := oneSidedLimits_canonical_H_raw_fields
    μ hμ hmoment C hClass hMean D hD left right hSequences Bm Bp hRaw

  rcases hFixed with ⟨hAgreement, hRawClass, hRawMean⟩
  rcases hRawOrder with ⟨hWithin, hCross⟩
  exact ⟨Bm, Bp, hAgreement, hRawClass, hRawMean,
    hWithin, hCross, hLimits⟩

end LPP.Busemann
