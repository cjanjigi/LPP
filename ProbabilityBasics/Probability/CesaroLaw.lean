/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Tactic

/-! # Cesàro averages of shifted sequence laws

This file averages the laws `ρ.map (sequenceShift^[j + 1])` for `j = 0, ..., n`.
Liggett (1985), equation (2.13), also uses positive shifts. For bounded
continuous test functions, the integral changes by at most
`2 * ‖f‖ / (n + 1)` under one further shift.
-/

public section

open MeasureTheory BoundedContinuousFunction
open scoped ENNReal

namespace LPPDifferentiability

/-- The literal left shift on real sequences. -/
@[expose] def sequenceShift (x : ℕ → ℝ) (k : ℕ) : ℝ := x (k + 1)

@[fun_prop] theorem continuous_sequenceShift : Continuous sequenceShift :=
  continuous_pi fun k => continuous_apply (k + 1)

@[fun_prop] theorem measurable_sequenceShift : Measurable sequenceShift :=
  continuous_sequenceShift.measurable

/-- The law viewed from origin `j + 1`. -/
@[expose] noncomputable def shiftedSequenceLaw
    (ρ : ProbabilityMeasure (ℕ → ℝ)) (j : ℕ) : ProbabilityMeasure (ℕ → ℝ) :=
  ρ.map (sequenceShift^[j + 1])

/-- The uniform mixture of the laws with origins `1, ..., n + 1`. -/
@[expose] noncomputable def cesaroSequenceLaw
    (ρ : ProbabilityMeasure (ℕ → ℝ)) (n : ℕ) : ProbabilityMeasure (ℕ → ℝ) :=
  ⟨((n + 1 : ℝ≥0∞)⁻¹) •
      ∑ j ∈ Finset.range (n + 1), (shiftedSequenceLaw ρ j : Measure (ℕ → ℝ)), by
    constructor
    simp [Measure.smul_apply, Measure.finsetSum_apply, ENNReal.inv_mul_cancel]⟩

/-- Integration under the actual finite mixture is the average of integrals. -/
theorem integral_cesaroSequenceLaw (ρ : ProbabilityMeasure (ℕ → ℝ)) (n : ℕ)
    (f : (ℕ → ℝ) →ᵇ ℝ) :
    ∫ x, f x ∂(cesaroSequenceLaw ρ n : Measure (ℕ → ℝ)) =
      (n + 1 : ℝ)⁻¹ * ∑ j ∈ Finset.range (n + 1),
        ∫ x, f x ∂(shiftedSequenceLaw ρ j : Measure (ℕ → ℝ)) := by
  change (∫ x, f x ∂((n + 1 : ℝ≥0∞)⁻¹ • _)) = _
  rw [integral_smul_measure, integral_finsetSum_measure (fun j _ => f.integrable _)]
  simp [ENNReal.toReal_add]

/-- Each summand is the test function evaluated at the corresponding shift. -/
theorem integral_shiftedSequenceLaw (ρ : ProbabilityMeasure (ℕ → ℝ)) (j : ℕ)
    (f : (ℕ → ℝ) →ᵇ ℝ) :
    ∫ x, f x ∂(shiftedSequenceLaw ρ j : Measure (ℕ → ℝ)) =
      ∫ x, f (sequenceShift^[j + 1] x) ∂(ρ : Measure (ℕ → ℝ)) := by
  exact integral_map (continuous_sequenceShift.iterate _).measurable.aemeasurable
    f.continuous.measurable.aestronglyMeasurable

/-- The source's bounded continuous test identity for the uniform mixture. -/
theorem integral_cesaroSequenceLaw_eq_average
    (ρ : ProbabilityMeasure (ℕ → ℝ)) (n : ℕ) (f : (ℕ → ℝ) →ᵇ ℝ) :
    ∫ x, f x ∂(cesaroSequenceLaw ρ n : Measure (ℕ → ℝ)) =
      (n + 1 : ℝ)⁻¹ * ∑ j ∈ Finset.range (n + 1),
        ∫ x, f (sequenceShift^[j + 1] x) ∂(ρ : Measure (ℕ → ℝ)) := by
  rw [integral_cesaroSequenceLaw]
  simp_rw [integral_shiftedSequenceLaw]

private theorem sum_successive_difference (a : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n, a (j + 1)) -
      (∑ j ∈ Finset.range n, a j) = a n - a 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Finset.sum_range_succ]
    linarith only [ih]

/-- Shifting the mixture cancels every interior term, leaving two endpoints. -/
theorem integral_cesaroSequenceLaw_shift_sub
    (ρ : ProbabilityMeasure (ℕ → ℝ)) (n : ℕ) (f : (ℕ → ℝ) →ᵇ ℝ) :
    (∫ x, f (sequenceShift x) ∂(cesaroSequenceLaw ρ n : Measure (ℕ → ℝ))) -
      (∫ x, f x ∂(cesaroSequenceLaw ρ n : Measure (ℕ → ℝ))) =
      (n + 1 : ℝ)⁻¹ *
        ((∫ x, f x ∂(shiftedSequenceLaw ρ (n + 1) : Measure (ℕ → ℝ))) -
          (∫ x, f x ∂(shiftedSequenceLaw ρ 0 : Measure (ℕ → ℝ)))) := by
  let g := f.compContinuous ⟨sequenceShift, continuous_sequenceShift⟩
  have hg (j : ℕ) :
      (∫ x, g x ∂(shiftedSequenceLaw ρ j : Measure (ℕ → ℝ))) =
      ∫ x, f x ∂(shiftedSequenceLaw ρ (j + 1) : Measure (ℕ → ℝ)) := by
    rw [integral_shiftedSequenceLaw, integral_shiftedSequenceLaw]
    congr 1
    funext x
    exact congrArg f (Function.iterate_succ_apply' sequenceShift (j + 1) x).symm
  change (∫ x, g x ∂_) - _ = _
  rw [integral_cesaroSequenceLaw, integral_cesaroSequenceLaw]
  simp_rw [hg]
  rw [← mul_sub, sum_successive_difference
    (fun j => ∫ x, f x ∂(shiftedSequenceLaw ρ j : Measure (ℕ → ℝ))) (n + 1)]

/-- The two endpoints give a uniform error tending to zero. -/
theorem norm_integral_cesaroSequenceLaw_shift_sub_le
    (ρ : ProbabilityMeasure (ℕ → ℝ)) (n : ℕ) (f : (ℕ → ℝ) →ᵇ ℝ) :
    ‖(∫ x, f (sequenceShift x) ∂(cesaroSequenceLaw ρ n : Measure (ℕ → ℝ))) -
      (∫ x, f x ∂(cesaroSequenceLaw ρ n : Measure (ℕ → ℝ)))‖ ≤
      2 * ‖f‖ / (n + 1 : ℝ) := by
  rw [integral_cesaroSequenceLaw_shift_sub, norm_mul,
    Real.norm_of_nonneg (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ n + 1))]
  calc
    _ ≤ (n + 1 : ℝ)⁻¹ * (‖f‖ + ‖f‖) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (norm_sub_le _ _).trans (add_le_add
        (f.norm_integral_le_norm _) (f.norm_integral_le_norm _))
    _ = _ := by ring

end LPPDifferentiability
