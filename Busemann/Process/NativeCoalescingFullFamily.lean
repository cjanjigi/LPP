/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Process.NativeFullFamily
public import Busemann.Process.RightmostPathCoalescenceApplications
public import Busemann.Frozen.Definitions.GeneralizedBusemann
import Busemann.Process.FullEventCocycles

@[expose] public section
open MeasureTheory ProbabilityTheory Filter LPPDifferentiability
open scoped BigOperators ENNReal Topology
namespace LPP.Busemann

/-- The original native coupled family also has coalescing rightmost paths
for each fixed tilt and both signs. Strong Existence, public source lines
379–412 and 456–464. -/
theorem exists_native_full_family_with_coalescing_rightmost_paths
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.NotAPointMass μ)
    (hmoment : LPPStatements.HasAbsoluteMomentAbove μ 2)
    (g : Quadrant → ℝ) (hg : IsExpectedRateShape μ g) :
    ∃ (P : Measure ProcessSample)
      (Bminus Bplus : SupportTilt g → Lattice → Lattice → ProcessSample → ℝ)
      (C : Set ProcessSample),
      P Set.univ = 1 ∧
      P.map processEnvironment = environmentLaw μ ∧
      (∀ z : Lattice, P.map (processShift z) = P) ∧
      Measurable (fun q : SupportTilt g × (Lattice × (Lattice × ProcessSample)) =>
        Bminus q.1 q.2.1 q.2.2.1 q.2.2.2) ∧
      Measurable (fun q : SupportTilt g × (Lattice × (Lattice × ProcessSample)) =>
        Bplus q.1 q.2.1 q.2.2.1 q.2.2.2) ∧
      HasBackwardIndependence g P Bminus Bplus ∧
      (∀ h : SupportTilt g, ∀ x y : Lattice,
        Integrable (Bminus h x y) P ∧ Integrable (Bplus h x y) P) ∧
      (∀ h : SupportTilt g, ∀ x : Lattice,
        (∫ s, Bminus h x (x + ((1 : ℤ), (0 : ℤ))) s ∂P) = -h.1.1 ∧
        (∫ s, Bplus h x (x + ((1 : ℤ), (0 : ℤ))) s ∂P) = -h.1.1 ∧
        (∫ s, Bminus h x (x + ((0 : ℤ), (1 : ℤ))) s ∂P) = -h.1.2 ∧
        (∫ s, Bplus h x (x + ((0 : ℤ), (1 : ℤ))) s ∂P) = -h.1.2) ∧
      MeasurableSet C ∧ P C = 1 ∧
      (∀ z : Lattice, ∀ s ∈ C, processShift z s ∈ C) ∧
      (∀ s ∈ C, ∀ h : SupportTilt g, ∀ x y z : Lattice,
        Bminus h (x + z) (y + z) s = Bminus h x y (processShift z s) ∧
        Bplus h (x + z) (y + z) s = Bplus h x y (processShift z s) ∧
        Bminus h x y s + Bminus h y z s = Bminus h x z s ∧
        Bplus h x y s + Bplus h y z s = Bplus h x z s) ∧
      (∀ s ∈ C, ∀ h : SupportTilt g,
        recovers_environment (processEnvironment s) (fun x y => Bminus h x y s) ∧
        recovers_environment (processEnvironment s) (fun x y => Bplus h x y s)) ∧
      (∀ s ∈ C, ∀ h : SupportTilt g, ∀ x : Lattice,
        Bminus h x (x + ((1 : ℤ), (0 : ℤ))) s ≥
          Bplus h x (x + ((1 : ℤ), (0 : ℤ))) s ∧
        Bminus h x (x + ((0 : ℤ), (1 : ℤ))) s ≤
          Bplus h x (x + ((0 : ℤ), (1 : ℤ))) s) ∧
      (∀ s ∈ C, ∀ h h' : SupportTilt g, h.1.1 < h'.1.1 → ∀ x : Lattice,
        Bplus h x (x + ((1 : ℤ), (0 : ℤ))) s ≥
          Bminus h' x (x + ((1 : ℤ), (0 : ℤ))) s ∧
        Bplus h x (x + ((0 : ℤ), (1 : ℤ))) s ≤
          Bminus h' x (x + ((0 : ℤ), (1 : ℤ))) s) ∧
      (∀ s ∈ C, ∀ h : SupportTilt g, ∀ x y : Lattice,
        ∀ hs : ℕ → SupportTilt g,
          (∀ n, (hs n).1.1 < h.1.1) → Tendsto hs atTop (𝓝 h) →
            Tendsto (fun n => Bminus (hs n) x y s) atTop (𝓝 (Bminus h x y s)) ∧
            Tendsto (fun n => Bplus (hs n) x y s) atTop (𝓝 (Bminus h x y s))) ∧
      (∀ s ∈ C, ∀ h : SupportTilt g, ∀ x y : Lattice,
        ∀ hs : ℕ → SupportTilt g,
          (∀ n, h.1.1 < (hs n).1.1) → Tendsto hs atTop (𝓝 h) →
            Tendsto (fun n => Bminus (hs n) x y s) atTop (𝓝 (Bplus h x y s)) ∧
            Tendsto (fun n => Bplus (hs n) x y s) atTop (𝓝 (Bplus h x y s))) ∧
      (∀ s ∈ C, ∀ h : SupportTilt g, ∀ x y : Lattice,
        Bminus h x y s = Bplus h x y s →
        ∀ hs : ℕ → SupportTilt g, Tendsto hs atTop (𝓝 h) →
          Tendsto (fun n => Bminus (hs n) x y s) atTop (𝓝 (Bminus h x y s)) ∧
          Tendsto (fun n => Bplus (hs n) x y s) atTop (𝓝 (Bminus h x y s))) ∧
      (∀ h : SupportTilt g, ∃ E : Set ProcessSample,
        MeasurableSet E ∧ E ⊆ C ∧ P E = 1 ∧
        ∀ s ∈ E, ∀ x y : Lattice,
          Bminus h x y s = Bplus h x y s) ∧
      (∀ h : SupportTilt g,
        IsGeneralizedBusemann P processShift processEnvironment (Bminus h) ∧
        HasCoalescingRightmostPaths P (Bminus h) ∧
        IsGeneralizedBusemann P processShift processEnvironment (Bplus h) ∧
        HasCoalescingRightmostPaths P (Bplus h))
 := by
  classical
  obtain ⟨P, Bminus, Bplus, C, hP, hMarginal, hShift, hMeasMinus,
    hMeasPlus, hBackward, hIntegrable, hMeans, hCMeas, hCProb, hCShift,
    hOnC, hRec, hWithinOrder, hCrossOrder, hLeftLimit, hRightLimit,
    hEqualityLimit, hEqualityEvent⟩ :=
      exists_native_full_family μ hμ hmoment g hg
  let : IsProbabilityMeasure P := ⟨hP⟩

  have hOnCMinus : ∀ s ∈ C, ∀ h : SupportTilt g, ∀ x y z : Lattice,
      Bminus h (x + z) (y + z) s = Bminus h x y (processShift z s) ∧
        Bminus h x y s + Bminus h y z s = Bminus h x z s := by
    intro s hs h x y z
    exact ⟨(hOnC s hs h x y z).1, (hOnC s hs h x y z).2.2.1⟩
  have hOnCPlus : ∀ s ∈ C, ∀ h : SupportTilt g, ∀ x y z : Lattice,
      Bplus h (x + z) (y + z) s = Bplus h x y (processShift z s) ∧
        Bplus h x y s + Bplus h y z s = Bplus h x z s := by
    intro s hs h x y z
    exact ⟨(hOnC s hs h x y z).2.1, (hOnC s hs h x y z).2.2.2⟩
  have hRecMinus : ∀ s ∈ C, ∀ h : SupportTilt g,
      recovers_environment (processEnvironment s) (fun x y => Bminus h x y s) := by
    intro s hs h
    exact (hRec s hs h).1
  have hRecPlus : ∀ s ∈ C, ∀ h : SupportTilt g,
      recovers_environment (processEnvironment s) (fun x y => Bplus h x y s) := by
    intro s hs h
    exact (hRec s hs h).2

  have hCocycleRecoveryMinus := cocycle_and_recovery_ae_of_full_event
    g P Bminus C hCMeas hCProb hMeasMinus hOnCMinus hRecMinus
  have hCocycleRecoveryPlus := cocycle_and_recovery_ae_of_full_event
    g P Bplus C hCMeas hCProb hMeasPlus hOnCPlus hRecPlus
  have hGeneralizedMinus (h : SupportTilt g) :
      IsGeneralizedBusemann P processShift processEnvironment (Bminus h) :=
    ⟨(hCocycleRecoveryMinus h).1, (hCocycleRecoveryMinus h).2,
      fun x y => (hIntegrable h x y).1⟩
  have hGeneralizedPlus (h : SupportTilt g) :
      IsGeneralizedBusemann P processShift processEnvironment (Bplus h) :=
    ⟨(hCocycleRecoveryPlus h).1, (hCocycleRecoveryPlus h).2,
      fun x y => (hIntegrable h x y).2⟩

  have hCoalescesMinus (h : SupportTilt g) :
      HasCoalescingRightmostPaths P (Bminus h) := by
    simpa using
      (hasCoalescingRightmostPaths_native_family_of_backward_independence
        μ hμ hmoment g P hP Bminus Bplus hMarginal hShift hMeasMinus
        hMeasPlus hBackward h false (hGeneralizedMinus h).1
        (hGeneralizedMinus h).2.1
        ((hGeneralizedMinus h).2.2 0 (1, 0))
        ((hGeneralizedMinus h).2.2 0 (0, 1)))
  have hCoalescesPlus (h : SupportTilt g) :
      HasCoalescingRightmostPaths P (Bplus h) := by
    simpa using
      (hasCoalescingRightmostPaths_native_family_of_backward_independence
        μ hμ hmoment g P hP Bminus Bplus hMarginal hShift hMeasMinus
        hMeasPlus hBackward h true (hGeneralizedPlus h).1
        (hGeneralizedPlus h).2.1
        ((hGeneralizedPlus h).2.2 0 (1, 0))
        ((hGeneralizedPlus h).2.2 0 (0, 1)))

  have hAdded : ∀ h : SupportTilt g,
      IsGeneralizedBusemann P processShift processEnvironment (Bminus h) ∧
        HasCoalescingRightmostPaths P (Bminus h) ∧
        IsGeneralizedBusemann P processShift processEnvironment (Bplus h) ∧
        HasCoalescingRightmostPaths P (Bplus h) := by
    intro h
    exact ⟨hGeneralizedMinus h, hCoalescesMinus h,
      hGeneralizedPlus h, hCoalescesPlus h⟩
  exact ⟨P, Bminus, Bplus, C, hP, hMarginal, hShift, hMeasMinus,
    hMeasPlus, hBackward, hIntegrable, hMeans, hCMeas, hCProb, hCShift,
    hOnC, hRec, hWithinOrder, hCrossOrder, hLeftLimit, hRightLimit,
    hEqualityLimit, hEqualityEvent, hAdded⟩

end LPP.Busemann
