/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.Process.RecoveringCocycleSupport
public import Busemann.Frozen.Definitions.CoalescingTilt
public import Busemann.Frozen.Definitions.SupportTilt
public import Martin2004.Statements.ShapeFacts

import LPP_Foundations.Analysis.AbsoluteMomentShape
import LPP_Foundations.Probability.TranslationEquiv
import ProbabilityBasics.Probability.NonconstantVariance

/-! A canonical coalescing tilt is supported by the supplied expected-rate shape. -/

@[expose] public section

open MeasureTheory LPPDifferentiability
open scoped ENNReal

namespace LPP.Busemann

/-- Every deterministic tilt in the canonical coalescing class is an
interior-contact support tilt of the expected-rate shape. This applies JR
arXiv:1810.03580v3, Lemma 4.5(a), to the canonical coalescing class. -/
theorem coalescingTilt_to_supportTilt
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.NotAPointMass μ)
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    (g : Quadrant → ℝ) (hg : IsExpectedRateShape μ g)
    (h : CoalescingTilt μ) :
    ∃ s : SupportTilt g, s.val = h.val := by
  let P : Measure Environment := environmentLaw μ
  let T : Lattice → Environment → Environment :=
    fun z ω => environmentTranslationEquiv z ω

  -- H membership supplies the actual canonical cocycle and its tilt identity.
  obtain ⟨B, hB, _, hTiltAE⟩ := h.property

  -- The canonical translations form a measure-preserving action on the environment.
  have hzero : ∀ ω : Environment, T 0 ω = ω := by
    intro ω
    funext x
    simp [T]
  have hadd : ∀ z w : Lattice, ∀ ω : Environment,
      T z (T w ω) = T (z + w) ω := by
    intro z w ω
    funext x
    simp [T, environmentTranslationEquiv_apply, add_comm, add_left_comm]
  have hShift : ∀ z : Lattice, MeasurePreserving (T z) P P := by
    intro z
    exact measurePreserving_environmentTranslationEquiv μ z
  have hWeightsMeas : Measurable (fun ω : Environment => ω) := measurable_id
  have hMarginal : P.map (fun ω : Environment => ω) = environmentLaw μ := by
    simp [P]
  have hWeightsShift : ∀ z x : Lattice, ∀ ω : Environment,
      (fun ω : Environment => ω) (T z ω) x =
        (fun ω : Environment => ω) ω (z + x) := by
    intro z x ω
    exact environmentTranslationEquiv_apply z ω x

  -- The original moment and non-point-mass assumptions give JR's variance input.
  have hSecondMoment : Integrable (fun t : ℝ => t ^ 2) μ :=
    (LPPDifferentiability.expected_rate_shape_boundary_asymptotics_and_second_moment_of_absolute_moment
      μ g hmoment hg).1
  have hNonconstant : ¬ ∃ c : ℝ, ∀ᵐ t ∂μ, t = c :=
    (LPPStatements.notAPointMass_iff_not_ae_const μ).mp hμ
  have hVariance : 0 < ∫ t : ℝ, (t - ∫ s : ℝ, s ∂μ) ^ 2 ∂μ :=
    ProbabilityBasics.integral_centered_sq_pos_of_not_ae_const
      μ hSecondMoment hNonconstant

  -- The structural witness supplies covariance, recovery, and both integrable edges.
  have hCocycle : is_shift_covariant_cocycle P T B := hB.1
  have hRecovery : recovers_weight_map_ae P (fun ω : Environment => ω) B := hB.2.1
  have hIntRight : Integrable (B 0 (1, 0)) P := hB.2.2 0 (1, 0)
  have hIntUp : Integrable (B 0 (0, 1)) P := hB.2.2 0 (0, 1)

  -- The joint support theorem supplies a random interior contact direction.
  have hJR :=
    recovering_cocycle_support_and_invariant_tilt Environment P μ T
      (fun ω : Environment => ω) B g
      hzero hadd hShift hWeightsMeas hMarginal hWeightsShift
      hmoment hVariance hg hCocycle hRecovery hIntRight hIntUp
  have hJRSupport : ∀ᵐ ω ∂P, ∃ ξ : InteriorDirection,
      -(invariantCocycleTilt P T (fun ω : Environment => ω) B hB ω) ∈
        quadrantSuperdifferential g ξ.val := hJR.1
  have hTiltValue : ∀ᵐ ω ∂P,
      invariantCocycleTilt P T (fun ω : Environment => ω) B hB ω = h.val := by
    exact hTiltAE
  have hBoth : ∀ᵐ ω ∂P,
      (∃ ξ : InteriorDirection,
        -(invariantCocycleTilt P T (fun ω : Environment => ω) B hB ω) ∈
          quadrantSuperdifferential g ξ.val) ∧
      invariantCocycleTilt P T (fun ω : Environment => ω) B hB ω = h.val :=
    hJRSupport.and hTiltValue
  obtain ⟨ω, ⟨hContact, hTilt⟩⟩ := hBoth.exists
  obtain ⟨ξ, hξ⟩ := hContact

  -- The two almost-sure statements give one deterministic supporting tilt.
  have hValue : -(h.val) ∈ quadrantSuperdifferential g ξ.val := by
    rw [← hTilt]
    exact hξ
  have hSupports : SupportsAt g ξ h.val := by
    intro z
    change (-h.val).1 * ((ξ.val.1 : ℝ) - (z.1 : ℝ)) +
      (-h.val).2 * ((ξ.val.2 : ℝ) - (z.2 : ℝ)) ≤ g ξ.val - g z
    exact hValue z
  refine ⟨⟨h.val, ⟨ξ, hSupports⟩⟩, rfl⟩

end LPP.Busemann
