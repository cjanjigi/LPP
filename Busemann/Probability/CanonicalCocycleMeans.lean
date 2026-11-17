/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen
-/
module

public import Busemann.Frozen.Definitions.InvariantCocycleTilt
public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-! Means of the two origin edges under a deterministic invariant tilt. -/

@[expose] public section

open MeasureTheory LPPDifferentiability

namespace LPP.Busemann

/-- If the full-action invariant tilt is deterministic, its two coordinates are
minus the ordinary means of the east and north origin edges. The tilt definition
is the accepted Strong Existence source, lines 354–358. -/
theorem canonical_origin_means_of_deterministic_invariant_tilt
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (B : Lattice → Lattice → Environment → ℝ)
    (hB : IsGeneralizedBusemann (environmentLaw μ)
      (fun z ω => environmentTranslationEquiv z ω) (fun ω => ω) B)
    (s : ℝ × ℝ)
    (hTilt : ∀ᵐ ω ∂environmentLaw μ,
      invariantCocycleTilt (environmentLaw μ)
        (fun z ω => environmentTranslationEquiv z ω) (fun ω => ω) B hB ω = s) :
    (∫ ω, B 0 ((1 : ℤ), (0 : ℤ)) ω ∂environmentLaw μ) = -s.1 ∧
    (∫ ω, B 0 ((0 : ℤ), (1 : ℤ)) ω ∂environmentLaw μ) = -s.2 := by
  classical
  let mEnv : MeasurableSpace Environment := inferInstance
  let I : MeasurableSpace Environment :=
    @latticeInvariantSigma Environment mEnv
      (fun z ω => environmentTranslationEquiv z ω)
  let : MeasurableSpace Environment := mEnv

  -- The full-action invariant sigma algebra lies below the ambient one.
  have hI : I ≤ mEnv :=
    (iInf_le (fun z : Lattice =>
      @MeasurableSpace.invariants Environment mEnv (environmentTranslationEquiv z))
      (0 : Lattice)).trans
      (MeasurableSpace.invariants_le (environmentTranslationEquiv (0 : Lattice)))
  let : IsFiniteMeasure ((environmentLaw μ).trim hI) := inferInstance
  let : SigmaFinite ((environmentLaw μ).trim hI) := inferInstance

  -- Generalized-cocycle integrability supplies each origin edge separately.
  have hEastInt : Integrable
      (fun ω : Environment => B 0 ((1 : ℤ), (0 : ℤ)) ω) (environmentLaw μ) :=
    hB.2.2 0 ((1 : ℤ), (0 : ℤ))
  have hNorthInt : Integrable
      (fun ω : Environment => B 0 ((0 : ℤ), (1 : ℤ)) ω) (environmentLaw μ) :=
    hB.2.2 0 ((0 : ℤ), (1 : ℤ))

  -- Unfold the literal definition, retaining the two distinct conditional means.
  have hTiltLocal : ∀ᵐ ω ∂environmentLaw μ,
      (-(environmentLaw μ)[B 0 ((1 : ℤ), (0 : ℤ)) | I] ω,
        -(environmentLaw μ)[B 0 ((0 : ℤ), (1 : ℤ)) | I] ω) = s := by
    simpa only [invariantCocycleTilt, I] using hTilt

  have hEastTilt : ∀ᵐ ω ∂environmentLaw μ,
      -(environmentLaw μ)[B 0 ((1 : ℤ), (0 : ℤ)) | I] ω = s.1 := by
    filter_upwards [hTiltLocal] with ω hω
    exact congrArg Prod.fst hω
  have hNorthTilt : ∀ᵐ ω ∂environmentLaw μ,
      -(environmentLaw μ)[B 0 ((0 : ℤ), (1 : ℤ)) | I] ω = s.2 := by
    filter_upwards [hTiltLocal] with ω hω
    exact congrArg Prod.snd hω
  have hEastCond : ∀ᵐ ω ∂environmentLaw μ,
      (environmentLaw μ)[B 0 ((1 : ℤ), (0 : ℤ)) | I] ω = -s.1 := by
    filter_upwards [hEastTilt] with ω hω
    have h := congrArg (fun x : ℝ => -x) hω
    simpa only [neg_neg] using h
  have hNorthCond : ∀ᵐ ω ∂environmentLaw μ,
      (environmentLaw μ)[B 0 ((0 : ℤ), (1 : ℤ)) | I] ω = -s.2 := by
    filter_upwards [hNorthTilt] with ω hω
    have h := congrArg (fun x : ℝ => -x) hω
    simpa only [neg_neg] using h

  -- Use the actual edge integrability in the conditional-expectation identity.
  have hEastCondIntegral :
      (∫ ω, (environmentLaw μ)[B 0 ((1 : ℤ), (0 : ℤ)) | I] ω
        ∂environmentLaw μ) =
      (∫ ω, B 0 ((1 : ℤ), (0 : ℤ)) ω ∂environmentLaw μ) := by
    simpa only [setIntegral_univ] using
      (setIntegral_condExp hI hEastInt (@MeasurableSet.univ Environment I))
  have hNorthCondIntegral :
      (∫ ω, (environmentLaw μ)[B 0 ((0 : ℤ), (1 : ℤ)) | I] ω
        ∂environmentLaw μ) =
      (∫ ω, B 0 ((0 : ℤ), (1 : ℤ)) ω ∂environmentLaw μ) := by
    simpa only [setIntegral_univ] using
      (setIntegral_condExp hI hNorthInt (@MeasurableSet.univ Environment I))

  -- Integrate the east conditional expectation, then its deterministic value.
  have hEastMean :
      (∫ ω, B 0 ((1 : ℤ), (0 : ℤ)) ω ∂environmentLaw μ) = -s.1 := by
    calc
      (∫ ω, B 0 ((1 : ℤ), (0 : ℤ)) ω ∂environmentLaw μ) =
          ∫ ω, (environmentLaw μ)[B 0 ((1 : ℤ), (0 : ℤ)) | I] ω
            ∂environmentLaw μ := hEastCondIntegral.symm
      _ = -s.1 := by
        rw [integral_congr_ae hEastCond]
        simp

  -- Repeat the same conditional-integral argument for the north edge.
  have hNorthMean :
      (∫ ω, B 0 ((0 : ℤ), (1 : ℤ)) ω ∂environmentLaw μ) = -s.2 := by
    calc
      (∫ ω, B 0 ((0 : ℤ), (1 : ℤ)) ω ∂environmentLaw μ) =
          ∫ ω, (environmentLaw μ)[B 0 ((0 : ℤ), (1 : ℤ)) | I] ω
            ∂environmentLaw μ := hNorthCondIntegral.symm
      _ = -s.2 := by
        rw [integral_congr_ae hNorthCond]
        simp

  exact ⟨hEastMean, hNorthMean⟩

end LPP.Busemann
