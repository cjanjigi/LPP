/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Process.RealQuantileShiftCovariance
public import Busemann.Process.RealQuantileCoalescence
public import Busemann.Frozen.Definitions.ForwardMeasurable
public import Busemann.Frozen.Definitions.RandomCocycle
public import Busemann.Frozen.Definitions.RecoveryAE
public import LPP_Foundations.Model.LastPassage.PassageDifferenceLimits
public import LPP_Foundations.Model.Paths.Coalescence
public import LPP_Foundations.Statements.ShapeDefinitions
import Busemann.Process.CanonicalGeodesicCocycleField
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

@[expose] public section
open MeasureTheory Filter ProbabilityTheory LPPDifferentiability
open scoped ENNReal Topology
namespace LPP.Busemann

/-- The same measurable conditional quantile sampler yields a forward cocycle
for almost every positive fixed parameter. The cocycle is characterized by
the finite passage differences of that sampler's original rays. Strong
Existence, lm:coal, B-def and lm:B-cK, lines 931–968 and 1007–1038. -/
theorem exists_real_quantile_sampler_with_forward_field_ae_parameter
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.NotAPointMass μ)
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    (P : Measure ProcessSample) [IsProbabilityMeasure P]
    (hMarginal : P.map processEnvironment = environmentLaw μ)
    (hShift : ∀ z : Lattice, P.map (processShift z) = P)
    (B : Lattice → Lattice → ProcessSample → ℝ)
    (hB : IsGeneralizedBusemann P processShift processEnvironment B)
    (hCoal : HasCoalescingRightmostPaths P B) :
    let κ : Lattice → Kernel Environment (ℕ → Lattice) :=
      fun u => condDistrib
        (fun a : ProcessSample =>
          rightmostCocyclePath (fun x y => B x y a) u)
        processEnvironment P
    ∃ q : Lattice → Environment → unitInterval → (ℕ → Lattice),
      (∀ u : Lattice, Measurable
        (fun a : Environment × unitInterval => q u a.1 a.2)) ∧
      (∀ᵐ ω ∂environmentLaw μ, ∀ (u : Lattice) (s : unitInterval),
        IsLocallyRightmostGeodesic ω u (q u ω s) ∧
        ∀ γ : ℕ → Lattice, IsLocallyRightmostGeodesic ω u γ →
          (pathSoutheastLE (q u ω s) γ ↔
            ENNReal.ofReal (s : ℝ) ≤
              (κ u) ω {η : ℕ → Lattice | pathSoutheastLE η γ})) ∧
      (∀ u : Lattice,
        (((environmentLaw μ).prod (volume : Measure unitInterval)).map
          (fun a : Environment × unitInterval => (a.1, q u a.1 a.2))) =
        P.map (fun a : ProcessSample =>
          (processEnvironment a,
            rightmostCocyclePath (fun x y => B x y a) u))) ∧
      (∀ᵐ ω ∂environmentLaw μ, ∀ (u z : Lattice) (s : unitInterval),
        q (u + z) ω s =
          fun n : ℕ => q u (environmentTranslationEquiv z ω) s n + z) ∧
      (∀ᵐ a ∂(environmentLaw μ).prod (volume : Measure unitInterval),
        ∀ u v : Lattice, paths_coalesce u v (q u a.1 a.2) (q v a.1 a.2)) ∧
      (∀ᵐ (s : unitInterval) ∂(volume : Measure unitInterval),
        0 < (s : ℝ) ∧
        ∃ C : Lattice → Lattice → Environment → ℝ,
          is_shift_covariant_cocycle (environmentLaw μ)
            (fun z ω => environmentTranslationEquiv z ω) C ∧
          recovers_weight_map_ae (environmentLaw μ)
            (fun ω : Environment => ω) C ∧
          IsForwardMeasurable C ∧
          ∀ᵐ ω ∂environmentLaw μ, ∀ u : Lattice,
            has_passage_difference_limits ω (q u ω s) (fun x y => C x y ω)) := by
  classical
  let κ : Lattice → Kernel Environment (ℕ → Lattice) :=
    fun u => condDistrib
      (fun a : ProcessSample =>
        rightmostCocyclePath (fun x y => B x y a) u)
      processEnvironment P
  obtain ⟨q, hQMeas, hQCDF, hQLaw, hQCov⟩ :=
    exists_measurable_real_rightmost_quantile_sampler_with_law_and_shift_covariance
      μ P hMarginal hShift B hB
  let coalesces : Environment → unitInterval → Prop := fun ω s =>
    ∀ u v : Lattice, paths_coalesce u v (q u ω s) (q v ω s)
  have hEval (u : Lattice) (i : ℕ) :
      Measurable (fun a : Environment × unitInterval => q u a.1 a.2 i) := by
    exact (measurable_pi_apply i).comp (hQMeas u)
  have hPairMeas (u v : Lattice) :
      MeasurableSet {a : Environment × unitInterval |
        ∃ m n : ℕ,
          u.1 + u.2 + (m : ℤ) = v.1 + v.2 + (n : ℤ) ∧
          ∀ k : ℕ, q u a.1 a.2 (m + k) = q v a.1 a.2 (n + k)} := by
    simp only [Set.ofPred_exists]
    refine MeasurableSet.iUnion fun m => MeasurableSet.iUnion fun n => ?_
    have hTail : MeasurableSet {a : Environment × unitInterval |
        ∀ k : ℕ, q u a.1 a.2 (m + k) = q v a.1 a.2 (n + k)} := by
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun k =>
        measurableSet_eq_fun (hEval u (m + k)) (hEval v (n + k))
    by_cases hLevel : u.1 + u.2 + (m : ℤ) = v.1 + v.2 + (n : ℤ)
    · simpa [hLevel] using hTail
    · simp [hLevel]
  have hCoalescesMeas :
      MeasurableSet {a : Environment × unitInterval | coalesces a.1 a.2} := by
    simp only [coalesces, paths_coalesce, Set.ofPred_forall]
    exact MeasurableSet.iInter fun u => MeasurableSet.iInter fun v => hPairMeas u v
  have hCoalescesAE :
      ∀ᵐ a ∂(environmentLaw μ).prod (volume : Measure unitInterval),
        coalesces a.1 a.2 := by
    simpa only [coalesces] using
      ae_coalescing_real_rightmost_quantile_family
        μ P hMarginal B hB hCoal q hQMeas hQCDF
  have hCoalescesSections :
      ∀ᵐ ω ∂environmentLaw μ,
        ∀ᵐ s ∂(volume : Measure unitInterval), coalesces ω s :=
    MeasureTheory.Measure.ae_ae_of_ae_prod hCoalescesAE
  have hParameterCoalesces :
      ∀ᵐ s ∂(volume : Measure unitInterval),
        ∀ᵐ ω ∂environmentLaw μ, coalesces ω s :=
    (MeasureTheory.Measure.ae_ae_comm hCoalescesMeas).mp hCoalescesSections
  have hPositive : ∀ᵐ (s : unitInterval) ∂(volume : Measure unitInterval),
      0 < (s : ℝ) := by
    have hNotZero : ∀ᵐ (s : unitInterval) ∂(volume : Measure unitInterval),
        s ≠ (0 : unitInterval) := by
      rw [ae_iff]
      simp
    filter_upwards [hNotZero] with s hs
    have hValueNeZero : (s : ℝ) ≠ 0 := by
      intro hzero
      exact hs (Subtype.ext hzero)
    exact lt_of_le_of_ne s.2.1 (Ne.symm hValueNeZero)
  refine ⟨q, hQMeas, hQCDF, hQLaw, hQCov, ?_, ?_⟩
  · simpa only [coalesces] using hCoalescesAE
  · filter_upwards [hPositive, hParameterCoalesces] with s hsPositive hsCoalesces
    refine ⟨hsPositive, ?_⟩
    let π : Lattice → Environment → (ℕ → Lattice) := fun u ω => q u ω s
    have hπSection : Measurable (fun ω : Environment => (ω, s)) :=
      measurable_id.prodMk measurable_const
    have hπMeas : ∀ u : Lattice, Measurable (π u) := by
      intro u
      dsimp only [π]
      exact (hQMeas u).comp hπSection
    have hπGeo : ∀ u : Lattice, ∀ᵐ ω ∂environmentLaw μ,
        IsLocallyRightmostGeodesic ω u (π u ω) := by
      intro u
      filter_upwards [hQCDF] with ω hω
      exact (hω u s).1
    have hπShift : ∀ u : Lattice, ∀ᵐ ω ∂environmentLaw μ,
        π u ω = (fun n : ℕ => π 0 (environmentTranslationEquiv u ω) n + u) := by
      intro u
      filter_upwards [hQCov] with ω hω
      simpa only [π, zero_add] using hω 0 u s
    have hπCoal : ∀ u v : Lattice, ∀ᵐ ω ∂environmentLaw μ,
        ∃ m n : ℕ,
          u.1 + u.2 + (m : ℤ) = v.1 + v.2 + (n : ℤ) ∧
          ∀ k : ℕ, (π u ω) (m + k) = (π v ω) (n + k) := by
      intro u v
      have hu := (ae_all_iff.mp hsCoalesces) u
      have huv := (ae_all_iff.mp hu) v
      simpa only [coalesces, paths_coalesce, π] using
        huv
    exact exists_forward_real_cocycle_of_coalescing_geodesic_family
      μ hμ hmoment π hπMeas hπGeo hπShift hπCoal

end LPP.Busemann
