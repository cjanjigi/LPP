/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.NativeCoalescingFullFamily
public import Busemann.Frozen.Process.RecoveringCocycleSupport
import LPP_Foundations.Analysis.AbsoluteMomentShape
import ProbabilityBasics.Probability.NonconstantVariance
import Martin2004.Statements.ShapeFacts
import Busemann.Process.Shifts

@[expose] public section

open MeasureTheory LPPDifferentiability
open scoped ENNReal

namespace LPP.Busemann

/-- One original native extended cocycle with its invariant tilt pinned at a
fixed ordinary extreme support; canonical H attainment requires representation. -/
theorem exists_native_extreme_support_cocycle_with_pinned_tilt
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.NotAPointMass μ)
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    (g : Quadrant → ℝ) (hg : IsExpectedRateShape μ g)
    (h : SupportTilt g) (ξ : Quadrant)
    (hξ : ξ ∈ closedUnitDirections)
    (hextreme : -h.val ∈
      Set.extremePoints ℝ (quadrantSuperdifferential g ξ)) :
    ∃ (P : Measure ProcessSample)
      (B : Lattice → Lattice → ProcessSample → ℝ),
      P Set.univ = 1 ∧
      P.map processEnvironment = environmentLaw μ ∧
      (∀ z : Lattice, P.map (processShift z) = P) ∧
      ∃ hB : IsGeneralizedBusemann P processShift processEnvironment B,
        HasCoalescingRightmostPaths P B ∧
        ∀ [IsProbabilityMeasure P],
          ∀ᵐ s ∂P,
            invariantCocycleTilt P processShift processEnvironment B hB s = h.val := by
  classical
  obtain ⟨P, Bminus, Bplus, C, hP, hMarginal, hShiftMap, hMeasMinus,
    hMeasPlus, hBackward, hIntegrable, hMeans, hCMeas, hCProb, hCShift,
    hOnC, hRec, hWithinOrder, hCrossOrder, hLeftLimit, hRightLimit,
    hEqualityLimit, hEqualityEvent, hAdded⟩ :=
      exists_native_full_family_with_coalescing_rightmost_paths
        μ hμ hmoment g hg
  let : IsProbabilityMeasure P := ⟨hP⟩
  let B : Lattice → Lattice → ProcessSample → ℝ := Bminus h
  have hB : IsGeneralizedBusemann P processShift processEnvironment B := by
    simpa [B] using (hAdded h).1
  have hCoalesces : HasCoalescingRightmostPaths P B := by
    simpa [B] using (hAdded h).2.1

  have hShiftMP (z : Lattice) : MeasurePreserving (processShift z) P P :=
    ⟨measurable_processShift z, hShiftMap z⟩
  have hShiftAdd : ∀ x y : Lattice, ∀ s : ProcessSample,
      processShift x (processShift y s) = processShift (x + y) s := by
    intro x y s
    exact (processShift_add x y s).symm
  have hWeightsShift : ∀ z x : Lattice, ∀ s : ProcessSample,
      processEnvironment (processShift z s) x = processEnvironment s (z + x) := by
    intro z x s
    rw [processEnvironment_processShift]
    exact environmentTranslationEquiv_apply z (processEnvironment s) x

  have hSecondMoment : Integrable (fun t : ℝ => t ^ 2) μ :=
    (LPPDifferentiability.expected_rate_shape_boundary_asymptotics_and_second_moment_of_absolute_moment
      μ g hmoment hg).1
  have hNonconstant : ¬ ∃ c : ℝ, ∀ᵐ t ∂μ, t = c :=
    (LPPStatements.notAPointMass_iff_not_ae_const μ).mp hμ
  have hVariance : 0 < ∫ t : ℝ, (t - ∫ s : ℝ, s ∂μ) ^ 2 ∂μ :=
    ProbabilityBasics.integral_centered_sq_pos_of_not_ae_const
      μ hSecondMoment hNonconstant

  have hRightIntegrable : Integrable (B 0 (1, 0)) P := hB.2.2 0 (1, 0)
  have hUpIntegrable : Integrable (B 0 (0, 1)) P := hB.2.2 0 (0, 1)
  have hJR := recovering_cocycle_support_and_invariant_tilt
    ProcessSample P μ processShift processEnvironment B g
    processShift_zero hShiftAdd hShiftMP
    measurable_fst hMarginal hWeightsShift hmoment hVariance hg
    hB.1 hB.2.1 hRightIntegrable hUpIntegrable

  let mProc : MeasurableSpace ProcessSample := inferInstance
  let I : MeasurableSpace ProcessSample :=
    ⨅ z : Lattice,
      @MeasurableSpace.invariants ProcessSample mProc (processShift z)
  let : MeasurableSpace ProcessSample := mProc
  have hI : I ≤ mProc :=
    (iInf_le (fun z : Lattice =>
      @MeasurableSpace.invariants ProcessSample mProc (processShift z))
      (0 : Lattice)).trans
      (MeasurableSpace.invariants_le (processShift (0 : Lattice)))
  let : IsFiniteMeasure (P.trim hI) := inferInstance
  let : SigmaFinite (P.trim hI) := inferInstance

  let jrMean : ℝ × ℝ :=
    (∫ s, -(P[B 0 (1, 0) | I] s) ∂P,
     ∫ s, -(P[B 0 (0, 1) | I] s) ∂P)
  have hRightMean :
      (∫ s, -(P[B 0 (1, 0) | I] s) ∂P) = h.val.1 := by
    have hNativeRight : (∫ s, B 0 (1, 0) s ∂P) = -h.val.1 := by
      simpa [B] using (hMeans h 0).1
    rw [integral_neg, integral_condExp hI, hNativeRight]
    simp
  have hUpMean :
      (∫ s, -(P[B 0 (0, 1) | I] s) ∂P) = h.val.2 := by
    have hNativeUp : (∫ s, B 0 (0, 1) s ∂P) = -h.val.2 := by
      simpa [B] using (hMeans h 0).2.2.1
    rw [integral_neg, integral_condExp hI, hNativeUp]
    simp
  have hJRMeanEq : jrMean = h.val := by
    dsimp [jrMean]
    exact Prod.ext hRightMean hUpMean
  have hExtremeMean : -jrMean ∈
      Set.extremePoints ℝ (quadrantSuperdifferential g ξ) := by
    rw [hJRMeanEq]
    exact hextreme

  have hPinnedRaw : ∀ᵐ s ∂P,
      (-(P[B 0 (1, 0) | I] s), -(P[B 0 (0, 1) | I] s)) = jrMean := by
    simpa only [latticeInvariantSigma, I, jrMean] using
      hJR.2.2 ξ hξ hExtremeMean
  have hPinned : ∀ᵐ s ∂P,
      invariantCocycleTilt P processShift processEnvironment B hB s = h.val := by
    filter_upwards [hPinnedRaw] with s hs
    rw [hJRMeanEq] at hs
    simpa only [invariantCocycleTilt, latticeInvariantSigma, I] using hs

  refine ⟨P, B, hP, hMarginal, hShiftMap, ?_⟩
  refine ⟨hB, hCoalesces, ?_⟩
  intro _hProbability
  exact hPinned

end LPP.Busemann
