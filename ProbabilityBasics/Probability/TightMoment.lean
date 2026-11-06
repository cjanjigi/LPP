/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.TightSubsequence
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.TightNormed
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Tactic.GCongr

/-!
# Tightness from first absolute moments

Markov's inequality controls the mass outside compact real balls. The
coordinate version supplies the weak-subsequence step after Liggett (2.12).
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace LPPDifferentiability

/-- A finite uniform bound on first absolute nonnegative integrals gives tightness. -/
theorem isTightMeasureSet_of_lintegral_abs_le (S : Set (Measure ℝ))
    (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hS : ∀ μ ∈ S, (∫⁻ x : ℝ, ENNReal.ofReal ‖x‖ ∂μ) ≤ C) :
    IsTightMeasureSet S := by
  apply isTightMeasureSet_of_tendsto_measure_norm_gt
  have hlim : Tendsto (fun r : ℝ => C / ENNReal.ofReal r) atTop (𝓝 0) := by
    simpa only [ENNReal.div_top] using
      (ENNReal.Tendsto.const_div ENNReal.tendsto_ofReal_atTop (Or.inr hC))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  refine iSup_le fun μ => iSup_le fun hμ => ?_
  calc
    μ {x : ℝ | r < ‖x‖} ≤ μ {x : ℝ | ENNReal.ofReal r ≤ ENNReal.ofReal ‖x‖} :=
      measure_mono fun x hx => ENNReal.ofReal_le_ofReal hx.le
    _ ≤ (∫⁻ x : ℝ, ENNReal.ofReal ‖x‖ ∂μ) / ENNReal.ofReal r :=
      meas_ge_le_lintegral_div
        (ENNReal.measurable_ofReal.comp measurable_norm).aemeasurable
        (ne_of_gt (ENNReal.ofReal_pos.mpr hr)) ENNReal.ofReal_ne_top
    _ ≤ C / ENNReal.ofReal r := by
      gcongr
      exact hS μ hμ

/-- Ordinary integrable first absolute moments supply the nonnegative-integral bound. -/
theorem isTightMeasureSet_of_integral_abs_le (μ : ℕ → Measure ℝ) (C : ℝ)
    (hμ : ∀ n, Integrable (fun x : ℝ => x) (μ n))
    (hbound : ∀ n, (∫ x : ℝ, |x| ∂μ n) ≤ C) :
    IsTightMeasureSet (Set.range μ) := by
  apply isTightMeasureSet_of_lintegral_abs_le _ (ENNReal.ofReal C) ENNReal.ofReal_ne_top
  rintro _ ⟨n, rfl⟩
  have heq := ofReal_integral_eq_lintegral_ofReal (hμ n).norm
    (ae_of_all (μ n) (fun x : ℝ => norm_nonneg x))
  rw [← heq]
  apply ENNReal.ofReal_le_ofReal
  simpa only [Real.norm_eq_abs] using hbound n

/-- Finite coordinate first-moment bounds produce a weak probability-law subsequence. -/
theorem exists_probabilityMeasure_tendsto_subseq_of_coordinate_moments
    (μ : ℕ → ProbabilityMeasure (ℕ → ℝ)) (C : ℕ → ℝ≥0∞)
    (hC : ∀ k, C k ≠ ∞)
    (hbound : ∀ n k, (∫⁻ x : ℕ → ℝ, ENNReal.ofReal ‖x k‖ ∂(μ n : Measure (ℕ → ℝ))) ≤ C k) :
    ∃ ν : ProbabilityMeasure (ℕ → ℝ), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (μ ∘ φ) atTop (𝓝 ν) := by
  apply exists_probabilityMeasure_tendsto_subseq_of_coordinate_tight μ
  intro k
  apply isTightMeasureSet_of_lintegral_abs_le _ (C k) (hC k)
  rintro _ ⟨n, rfl⟩
  change (∫⁻ x : ℝ, ENNReal.ofReal ‖x‖
    ∂Measure.map (Function.eval k) (μ n : Measure (ℕ → ℝ))) ≤ C k
  rw [lintegral_map (f := fun x : ℝ => ENNReal.ofReal ‖x‖)
    (ENNReal.measurable_ofReal.comp measurable_norm)
    (measurable_pi_apply k)]
  exact hbound n k

end LPPDifferentiability
