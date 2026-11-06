/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.MaximalErgodicFinite
public import ProbabilityBasics.Probability.HardCutoff
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Linarith

/-!
# Finite maximal inequality for integrable observables

Keane and Petersen (2006), p. 249. Exact finite-orbit stabilization justifies
strict-event convergence, including at threshold atoms. Global measurability
specifies the representatives used in the orbit events.
-/

public section

open MeasureTheory Set Filter
open scoped Topology

namespace LPPDifferentiability

private theorem hardCutoff_abs_le_level {Ω : Type*} (f : Ω → ℝ)
    {L : ℝ} (hL : 0 ≤ L) (ω : Ω) : |hardCutoff f L ω| ≤ L := by
  by_cases h : |f ω| ≤ L
  · simpa only [hardCutoff, ite_eq_left h] using h
  · simpa only [hardCutoff, ite_eq_right h, abs_zero] using hL

private theorem cutoff_mask_eventually_eq {Ω : Type*} (T : Ω → Ω)
    (f threshold : Ω → ℝ) (N : ℕ) (ω : Ω) :
    ∀ᶠ n : ℕ in atTop,
      (finiteMaximalEvent T (hardCutoff f ((n : ℝ) + 1)) threshold N).indicator
        (fun x => hardCutoff f ((n : ℝ) + 1) x - threshold x) ω =
      (finiteMaximalEvent T f threshold N).indicator (fun x => f x - threshold x) ω := by
  classical
  obtain ⟨L₀, hL₀⟩ := hardCutoff_eventually_eq_finite_orbit f T ω (N + 1)
  obtain ⟨m, hm⟩ := exists_nat_gt L₀
  filter_upwards [eventually_ge_atTop m] with n hn
  have hL : L₀ ≤ (n : ℝ) + 1 := by
    have hmn : (m : ℝ) ≤ n := Nat.cast_le.mpr hn
    linarith only [hm, hmn]
  have hvalues := hL₀ ((n : ℝ) + 1) hL
  have hstart : hardCutoff f ((n : ℝ) + 1) ω = f ω := by
    simpa only [Function.iterate_zero, id_eq] using hvalues 0 (by omega)
  have hevent : ω ∈ finiteMaximalEvent T (hardCutoff f ((n : ℝ) + 1)) threshold N ↔
      ω ∈ finiteMaximalEvent T f threshold N := by
    change (∃ k, 1 ≤ k ∧ k ≤ N ∧ threshold ω < orbitAverage _ T k ω) ↔
      (∃ k, 1 ≤ k ∧ k ≤ N ∧ threshold ω < orbitAverage f T k ω)
    constructor
    · rintro ⟨k, hk, hkN, ha⟩
      have heq := orbitAverage_eq_of_eq_finite_orbit _ f T ω (N+1) k
        (by omega) hvalues
      exact ⟨k, hk, hkN, by rwa [heq] at ha⟩
    · rintro ⟨k, hk, hkN, ha⟩
      have heq := orbitAverage_eq_of_eq_finite_orbit (hardCutoff f ((n : ℝ)+1)) f T ω
        (N+1) k (by omega) hvalues
      exact ⟨k, hk, hkN, by rwa [heq]⟩
  simp only [Set.indicator_apply, hevent, hstart]

/-- The finite maximal inequality for integrable observables and integrable
almost everywhere invariant thresholds. Global measurability is explicit. -/
theorem integral_finiteMaximalEvent_nonneg_of_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω} {f threshold : Ω → ℝ}
    (hT : MeasurePreserving T μ μ) (hf : Measurable f) (hthreshold : Measurable threshold)
    (hfint : Integrable f μ) (hthresholdint : Integrable threshold μ)
    (hthresholdinv : ∀ᵐ ω ∂μ, threshold (T ω) = threshold ω) (N : ℕ) :
    0 ≤ ∫ ω in finiteMaximalEvent T f threshold N, (f ω - threshold ω) ∂μ := by
  classical
  let F : ℕ → Ω → ℝ := fun n =>
    (finiteMaximalEvent T (hardCutoff f ((n : ℝ)+1)) threshold N).indicator
      (fun ω => hardCutoff f ((n : ℝ)+1) ω - threshold ω)
  let q := (finiteMaximalEvent T f threshold N).indicator (fun ω => f ω - threshold ω)
  have hE (n : ℕ) := measurableSet_finiteMaximalEvent hT.measurable
    (measurable_hardCutoff f hf ((n : ℝ)+1)) hthreshold N
  have hFmeas (n : ℕ) : AEStronglyMeasurable (F n) μ :=
    (((measurable_hardCutoff f hf ((n : ℝ)+1)).sub hthreshold).indicator (hE n)).aestronglyMeasurable
  have hbound (n : ℕ) : ∀ᵐ ω ∂μ, ‖F n ω‖ ≤ |f ω| + |threshold ω| := by
    apply Eventually.of_forall
    intro ω
    dsimp only [F]
    by_cases hω : ω ∈ finiteMaximalEvent T (hardCutoff f ((n : ℝ)+1)) threshold N
    · rw [indicator_of_mem hω, Real.norm_eq_abs]
      exact (abs_sub _ _).trans (add_le_add (hardCutoff_abs_le f _ ω) le_rfl)
    · rw [indicator_of_notMem hω, norm_zero]
      exact add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => F n ω) atTop (𝓝 (q ω)) := by
    apply Eventually.of_forall
    intro ω
    apply tendsto_const_nhds.congr'
    filter_upwards [cutoff_mask_eventually_eq T f threshold N ω] with n hn
    exact hn.symm
  have hint := tendsto_integral_of_dominated_convergence (fun ω => |f ω| + |threshold ω|)
    hFmeas (hfint.abs.add hthresholdint.abs) hbound hlim
  have hnonneg (n : ℕ) : 0 ≤ ∫ ω, F n ω ∂μ := by
    have h := integral_finiteMaximalEvent_nonneg hT
      (measurable_hardCutoff f hf ((n : ℝ)+1)) hthreshold hthresholdint hthresholdinv
      (M := (n : ℝ)+1) (by positivity)
      (hardCutoff_abs_le_level f (by positivity)) N
    simpa only [F, integral_indicator (hE n)] using h
  have h := ge_of_tendsto hint (Eventually.of_forall hnonneg)
  simpa only [q, integral_indicator (measurableSet_finiteMaximalEvent
    hT.measurable hf hthreshold N)] using h

end LPPDifferentiability
