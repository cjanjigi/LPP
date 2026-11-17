/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.StrongExistence.Definitions.SkorokhodRealization

import Busemann.Process.StrongCoupledFields
import Busemann.Process.CoalescingTiltTimeClosedness
import Busemann.Process.StrongSkorokhodRealization
import Busemann.Process.StrongProcessUniqueness

@[expose] public section
open MeasureTheory Filter LPPDifferentiability LPP.Busemann
open scoped ENNReal Topology
namespace LPP.Busemann.Proof

/-- The full Busemann process on the canonical space is
unique under the six source properties. The same pair has a measurable Skorokhod realization. See Theorem 3.11. -/
theorem exists_unique_strong_busemann_process :
∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
  LPPStatements.NotAPointMass μ →
  (∃ p : ℝ, 2 < p ∧ (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞) →
  ∃ Bm Bp : StrongField μ,
    BranchAgreement μ Bm Bp ∧ ForwardCoalescingClass μ Bm Bp ∧ MeanTilt μ Bm ∧
    WithinTiltOrder μ Bm Bp ∧ StrictCrossTiltOrder μ Bm Bp ∧ OneSidedLimits μ Bm Bp ∧
    SkorokhodRealization μ Bm Bp ∧
    (∀ Bm' Bp' : StrongField μ,
      (BranchAgreement μ Bm' Bp' ∧ ForwardCoalescingClass μ Bm' Bp' ∧
       MeanTilt μ Bm' ∧ WithinTiltOrder μ Bm' Bp' ∧
       StrictCrossTiltOrder μ Bm' Bp' ∧ OneSidedLimits μ Bm' Bp') →
      ∀ᵐ ω ∂environmentLaw μ, ∀ (h : CoalescingTilt μ) (x y : Lattice),
        Bm' h x y ω = Bm h x y ω ∧ Bp' h x y ω = Bp h x y ω) := by
  intro μ _ hμ hmoment
  obtain ⟨Bm, Bp, hAgreement, hClass, hMean, hWithin, hCross, hLimits⟩ :=
    exists_strong_coupled_fields_of_absolute_moment μ hμ hmoment

  -- Realize the exact six-property pair using the actual closed time set.
  have hClosed : IsClosed (timeSet μ) :=
    isClosed_timeSet_of_absolute_moment μ hμ hmoment
  have hRealization := skorokhodRealization_of_strong_process_properties
    μ hμ hmoment Bm Bp hClosed hAgreement hClass hMean hWithin hCross hLimits

  -- The uniqueness theorem compares every competing six-property pair.
  have hFirst :
      BranchAgreement μ Bm Bp ∧ ForwardCoalescingClass μ Bm Bp ∧
        MeanTilt μ Bm ∧ WithinTiltOrder μ Bm Bp ∧
        StrictCrossTiltOrder μ Bm Bp ∧ OneSidedLimits μ Bm Bp :=
    ⟨hAgreement, hClass, hMean, hWithin, hCross, hLimits⟩
  have hUnique :
      ∀ Bm' Bp' : StrongField μ,
        (BranchAgreement μ Bm' Bp' ∧ ForwardCoalescingClass μ Bm' Bp' ∧
          MeanTilt μ Bm' ∧ WithinTiltOrder μ Bm' Bp' ∧
          StrictCrossTiltOrder μ Bm' Bp' ∧ OneSidedLimits μ Bm' Bp') →
        ∀ᵐ ω ∂environmentLaw μ, ∀ (h : CoalescingTilt μ) (x y : Lattice),
          Bm' h x y ω = Bm h x y ω ∧ Bp' h x y ω = Bp h x y ω := by
    intro Bm' Bp' hSecond
    exact ae_eq_strong_busemann_process_of_six_properties
      μ hμ hmoment Bm Bp Bm' Bp' hFirst hSecond

  exact ⟨Bm, Bp, hAgreement, hClass, hMean, hWithin, hCross, hLimits,
    hRealization, hUnique⟩

end LPP.Busemann.Proof
