/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.CanonicalForwardCocycleVersion
public import Busemann.Frozen.StrongExistence.Definitions.StrongField
public import Busemann.Frozen.Definitions.InvariantCocycleTilt
public import Busemann.Geometry.CoalescingTiltTimeIndex
public import ProbabilityBasics.Analysis.CountableSidedSampleSet

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-! Select one literal forward version for every actual coalescing tilt. -/

@[expose] public section

open MeasureTheory Filter LPPDifferentiability
open scoped ENNReal Topology

namespace LPP.Busemann

/-- Each actual coalescing tilt has a selected canonical forward field with
that full deterministic invariant tilt. This is the selection step in Strong
Existence, lines 1194–1217. -/
theorem exists_forward_canonical_field_on_coalescingTilts
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.NotAPointMass μ)
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞) :
    ∃ C : StrongField μ,
      ∀ h : CoalescingTilt μ,
        ∃ hC : IsGeneralizedBusemann (environmentLaw μ)
          (fun z ω => environmentTranslationEquiv z ω) (fun ω => ω) (C h),
          HasCoalescingRightmostPaths (environmentLaw μ) (C h) ∧
          IsForwardMeasurable (C h) ∧
          (∀ᵐ ω ∂environmentLaw μ,
            invariantCocycleTilt (environmentLaw μ)
              (fun z ω => environmentTranslationEquiv z ω) (fun ω => ω)
              (C h) hC ω = h.val) := by
  classical

  -- For each actual H member, version its original field while retaining the
  -- original coalescing witness and deterministic full-action tilt.
  have hVersion (h : CoalescingTilt μ) :
      ∃ V : Lattice → Lattice → Environment → ℝ,
        ∃ hV : IsGeneralizedBusemann (environmentLaw μ)
          (fun z ω => environmentTranslationEquiv z ω) (fun ω => ω) V,
          HasCoalescingRightmostPaths (environmentLaw μ) V ∧
          IsForwardMeasurable V ∧
          (∀ᵐ ω ∂environmentLaw μ,
            invariantCocycleTilt (environmentLaw μ)
              (fun z ω => environmentTranslationEquiv z ω)
              (fun ω => ω) V hV ω = h.val) := by
    obtain ⟨B, hB, hCoalB, hTiltB⟩ := h.property
    obtain ⟨V, hV, hCoalV, hForwardV, hVersionAE⟩ :=
      exists_forward_version_of_coalescing_canonical_cocycle
        μ hμ hmoment B hB hCoalB

    -- Save the ambient measurable space, use the same full-action invariant
    -- sigma algebra for both edges, then restore the ambient instance.
    let P : Measure Environment := environmentLaw μ
    let T : Lattice → Environment → Environment :=
      fun z ω => environmentTranslationEquiv z ω
    let mEnv : MeasurableSpace Environment := inferInstance
    let I : MeasurableSpace Environment :=
      @latticeInvariantSigma Environment mEnv T
    let : MeasurableSpace Environment := mEnv

    have hEastAE :
        (fun ω => V 0 ((1 : ℤ), (0 : ℤ)) ω) =ᵐ[P]
          (fun ω => B 0 ((1 : ℤ), (0 : ℤ)) ω) := by
      filter_upwards [hVersionAE] with ω hω
      exact hω 0 ((1 : ℤ), (0 : ℤ))
    have hNorthAE :
        (fun ω => V 0 ((0 : ℤ), (1 : ℤ)) ω) =ᵐ[P]
          (fun ω => B 0 ((0 : ℤ), (1 : ℤ)) ω) := by
      filter_upwards [hVersionAE] with ω hω
      exact hω 0 ((0 : ℤ), (1 : ℤ))

    -- Transfer both conditional edge expectations on that same sigma algebra.
    have hEastCond :
        P[V 0 ((1 : ℤ), (0 : ℤ)) | I] =ᵐ[P]
          P[B 0 ((1 : ℤ), (0 : ℤ)) | I] :=
      condExp_congr_ae hEastAE
    have hNorthCond :
        P[V 0 ((0 : ℤ), (1 : ℤ)) | I] =ᵐ[P]
          P[B 0 ((0 : ℤ), (1 : ℤ)) | I] :=
      condExp_congr_ae hNorthAE
    have hTiltV : ∀ᵐ ω ∂P,
        invariantCocycleTilt P T (fun ω => ω) V hV ω = h.val := by
      filter_upwards [hEastCond, hNorthCond, hTiltB] with ω hEast hNorth hTilt
      apply Prod.ext
      · change -(P[V 0 ((1 : ℤ), (0 : ℤ)) | I] ω) = h.val.1
        have hTiltEast := congrArg Prod.fst hTilt
        change -(P[B 0 ((1 : ℤ), (0 : ℤ)) | I] ω) = h.val.1 at hTiltEast
        rw [hEast]
        exact hTiltEast
      · change -(P[V 0 ((0 : ℤ), (1 : ℤ)) | I] ω) = h.val.2
        have hTiltNorth := congrArg Prod.snd hTilt
        change -(P[B 0 ((0 : ℤ), (1 : ℤ)) | I] ω) = h.val.2 at hTiltNorth
        rw [hNorth]
        exact hTiltNorth
    exact ⟨V, hV, hCoalV, hForwardV, hTiltV⟩

  -- Choose a representative separately for every H member, with no common
  -- almost-sure event asserted across the entire subtype.
  choose V hV hRest using hVersion
  let C : StrongField μ := fun h => V h
  refine ⟨C, ?_⟩
  intro h
  exact ⟨hV h, (hRest h).1, (hRest h).2.1, (hRest h).2.2⟩

end LPP.Busemann
