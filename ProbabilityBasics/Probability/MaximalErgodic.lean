/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.MaximalErgodicIntegrable
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The integrable maximal ergodic inequality

The increasing-horizon dominated convergence step of Keane and Petersen
(2006), p. 249. The threshold is integrable; the broader positive-part-only
extended-integral version is not asserted.
-/

public section

open MeasureTheory Set Filter
open scoped Topology

namespace LPPDifferentiability

/-- Some positive-time forward average strictly exceeds the threshold. -/
@[expose] def maximalEvent {Ω : Type*} (T : Ω → Ω) (f threshold : Ω → ℝ) : Set Ω :=
  {ω | ∃ k : ℕ, 1 ≤ k ∧ threshold ω < orbitAverage f T k ω}

/-- Finite maximal events increase with the horizon. -/
theorem finiteMaximalEvent_mono {Ω : Type*} (T : Ω → Ω) (f threshold : Ω → ℝ) :
    Monotone (finiteMaximalEvent T f threshold) := by
  intro N M hNM ω hω
  obtain ⟨k, hk, hkN, ha⟩ := hω
  exact ⟨k, hk, hkN.trans hNM, ha⟩

/-- The full maximal event is the union of its finite horizons. -/
theorem maximalEvent_eq_iUnion {Ω : Type*} (T : Ω → Ω) (f threshold : Ω → ℝ) :
    maximalEvent T f threshold = ⋃ N : ℕ, finiteMaximalEvent T f threshold N := by
  ext ω
  constructor
  · rintro ⟨k, hk, ha⟩
    exact mem_iUnion.mpr ⟨k, k, hk, le_rfl, ha⟩
  · intro hω
    obtain ⟨N, k, hk, _, ha⟩ := mem_iUnion.mp hω
    exact ⟨k, hk, ha⟩

/-- The full event is measurable for globally measurable representatives. -/
theorem measurableSet_maximalEvent {Ω : Type*} [MeasurableSpace Ω]
    {T : Ω → Ω} {f threshold : Ω → ℝ} (hT : Measurable T) (hf : Measurable f)
    (hthreshold : Measurable threshold) : MeasurableSet (maximalEvent T f threshold) := by
  rw [maximalEvent_eq_iUnion]
  exact MeasurableSet.iUnion fun N => measurableSet_finiteMaximalEvent hT hf hthreshold N

/-- The maximal ergodic inequality for an integrable observable and an
integrable almost everywhere invariant threshold on a probability space.
Global measurability explicitly chooses the orbit representatives. -/
theorem integral_maximalEvent_nonneg {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω} {f threshold : Ω → ℝ}
    (hT : MeasurePreserving T μ μ) (hf : Measurable f) (hthreshold : Measurable threshold)
    (hfint : Integrable f μ) (hthresholdint : Integrable threshold μ)
    (hthresholdinv : ∀ᵐ ω ∂μ, threshold (T ω) = threshold ω) :
    0 ≤ ∫ ω in maximalEvent T f threshold, (f ω - threshold ω) ∂μ := by
  classical
  let F : ℕ → Ω → ℝ := fun N =>
    (finiteMaximalEvent T f threshold N).indicator (fun ω => f ω - threshold ω)
  let q := (maximalEvent T f threshold).indicator (fun ω => f ω - threshold ω)
  have hE (N : ℕ) := measurableSet_finiteMaximalEvent hT.measurable hf hthreshold N
  have hFmeas (N : ℕ) : AEStronglyMeasurable (F N) μ :=
    ((hf.sub hthreshold).indicator (hE N)).aestronglyMeasurable
  have hbound (N : ℕ) : ∀ᵐ ω ∂μ, ‖F N ω‖ ≤ |f ω| + |threshold ω| := by
    apply Eventually.of_forall
    intro ω
    dsimp only [F]
    by_cases hω : ω ∈ finiteMaximalEvent T f threshold N
    · rw [indicator_of_mem hω, Real.norm_eq_abs]
      exact abs_sub _ _
    · rw [indicator_of_notMem hω, norm_zero]
      exact add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun N => F N ω) atTop (𝓝 (q ω)) := by
    apply Eventually.of_forall
    intro ω
    apply tendsto_const_nhds.congr'
    by_cases hω : ω ∈ maximalEvent T f threshold
    · obtain ⟨k, hk, ha⟩ := hω
      filter_upwards [eventually_ge_atTop k] with N hN
      have hfinite : ω ∈ finiteMaximalEvent T f threshold N := ⟨k, hk, hN, ha⟩
      have hfull : ω ∈ maximalEvent T f threshold := ⟨k, hk, ha⟩
      simp only [F, q, indicator_of_mem hfinite, indicator_of_mem hfull]
    · apply Eventually.of_forall
      intro N
      have hfinite : ω ∉ finiteMaximalEvent T f threshold N := by
        rintro ⟨k, hk, _, ha⟩
        exact hω ⟨k, hk, ha⟩
      simp only [F, q, indicator_of_notMem hfinite, indicator_of_notMem hω]
  have hint := tendsto_integral_of_dominated_convergence (fun ω => |f ω| + |threshold ω|)
    hFmeas (hfint.abs.add hthresholdint.abs) hbound hlim
  have hnonneg (N : ℕ) : 0 ≤ ∫ ω, F N ω ∂μ := by
    simpa only [F, integral_indicator (hE N)] using
      integral_finiteMaximalEvent_nonneg_of_integrable hT hf hthreshold hfint
        hthresholdint hthresholdinv N
  have h := ge_of_tendsto hint (Eventually.of_forall hnonneg)
  simpa only [q, integral_indicator (measurableSet_maximalEvent hT.measurable hf hthreshold)] using h

end LPPDifferentiability
