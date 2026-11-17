/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Process.NativeExtremeSupportCocycle
public import Busemann.Process.PinnedOriginalSpaceCocycle
public import Busemann.Frozen.Definitions.CoalescingTilts
public import Busemann.Probability.CanonicalInvariantConditionalMean

import Mathlib.Tactic.Ring

@[expose] public section
open MeasureTheory LPPDifferentiability
open scoped ENNReal
namespace LPP.Busemann

/-- An extreme supporting tilt furnished by the native coupled cocycle is
attained by a coalescing generalized Busemann cocycle on the original iid
environment. Strong Existence, definition of H and first inclusion,
lines 576–592, using the pinned original-space reduction at 1069–1103. -/
theorem extreme_support_tilt_mem_coalescingTilts
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.NotAPointMass μ)
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    (g : Quadrant → ℝ) (hg : IsExpectedRateShape μ g)
    (h : SupportTilt g) (ξ : Quadrant)
    (hξ : ξ ∈ closedUnitDirections)
    (hextreme : -h.val ∈
      Set.extremePoints ℝ (quadrantSuperdifferential g ξ)) :
    h.val ∈ coalescingTilts μ := by
  -- Obtain the actual coupled sample and pinned invariant tilt at h.val.
  obtain ⟨P, B, hPmass, hMarginal, hShift, hB, hCoalescing, hPinned⟩ :=
    exists_native_extreme_support_cocycle_with_pinned_tilt
      μ hμ hmoment g hg h ξ hξ hextreme

  -- The native measure mass supplies the probability instance required by
  -- the original-space assembly and the pinned almost-sure identity.
  let : IsProbabilityMeasure P := ⟨hPmass⟩

  -- Pull back one original-environment field from this same coupled P and B.
  obtain ⟨C, hC, _, hCoalescingC, hMeanEast, hMeanNorth, _⟩ :=
    exists_original_forward_cocycle_of_pinned_coupled_cocycle
      μ hμ hmoment P hMarginal hShift B hB hCoalescing h.val hPinned

  -- Convert the ordinary means of C into the two conditional invariant means.
  have hInvariantTilt :
      ∀ᵐ ω ∂environmentLaw μ,
        invariantCocycleTilt (environmentLaw μ)
          (fun z ω => environmentTranslationEquiv z ω) (fun ω => ω)
          C hC ω = h.val := by
    let mEnv : MeasurableSpace Environment := inferInstance
    let I : MeasurableSpace Environment :=
      @latticeInvariantSigma Environment mEnv
        (fun z ω => environmentTranslationEquiv z ω)
    let : MeasurableSpace Environment := mEnv
    have hEast := canonical_condExp_full_invariants_eq_mean μ
      (C 0 ((1 : ℤ), (0 : ℤ))) (hC.2.2 0 ((1 : ℤ), (0 : ℤ)))
    have hNorth := canonical_condExp_full_invariants_eq_mean μ
      (C 0 ((0 : ℤ), (1 : ℤ))) (hC.2.2 0 ((0 : ℤ), (1 : ℤ)))
    filter_upwards [hEast, hNorth] with ω hEastω hNorthω
    apply Prod.ext
    · change -((environmentLaw μ)[C 0 ((1 : ℤ), (0 : ℤ)) | I] ω) = h.val.1
      rw [hEastω, hMeanEast]
      ring
    · change -((environmentLaw μ)[C 0 ((0 : ℤ), (1 : ℤ)) | I] ω) = h.val.2
      rw [hNorthω, hMeanNorth]
      ring

  -- H asks for this one generalized-Busemann witness, its coalescing paths,
  -- and the almost-sure invariant tilt. The proof binder hC is not another
  -- conjunct in the definition.
  change ∃ C' : Lattice → Lattice → Environment → ℝ,
    ∃ hC' : IsGeneralizedBusemann (environmentLaw μ)
      (fun z ω => environmentTranslationEquiv z ω) (fun ω => ω) C',
      HasCoalescingRightmostPaths (environmentLaw μ) C' ∧
      ∀ᵐ ω ∂environmentLaw μ,
        invariantCocycleTilt (environmentLaw μ)
          (fun z ω => environmentTranslationEquiv z ω) (fun ω => ω)
          C' hC' ω = h.val
  exact ⟨C, hC, hCoalescingC, hInvariantTilt⟩

end LPP.Busemann
