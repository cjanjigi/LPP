/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.FiniteBadMaskLaw

/-!
# Normalizing a finite threshold cube

This file normalizes the product measure restricted to a threshold cube, that is, the set of
configurations with a fixed pattern of values below and at least `-T`. Every normalized statement
assumes that the cube has positive mass. The endpoint `-T` belongs to the good half-line, the set
of values at least `-T`.
-/

public section

open MeasureTheory

namespace LPPDifferentiability

/-- Positive mass of the cube implies positive mass of every one-site factor. -/
theorem finite_threshold_mask_factor_mass_pos {I : Type*} [Fintype I]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (T : ℝ) (hT : 0 < T) (b : I → Bool)
    (hC : 0 < (Measure.pi (fun _ : I => μ))
      (finiteThresholdMaskCube T b)) (i : I) :
    0 < μ {y : ℝ | if b i then y < -T else -T ≤ y} := by
  rw [finite_threshold_mask_cube_measure μ T hT b] at hC
  exact bot_lt_iff_ne_bot.mpr
    (Finset.prod_ne_zero_iff.mp hC.ne' i (Finset.mem_univ i))

/-- Factor masses are finite, because the one-site law is a probability measure. -/
theorem finite_threshold_mask_factor_mass_lt_top
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (T : ℝ) (c : Bool) :
    μ {y : ℝ | if c then y < -T else -T ≤ y} < ⊤ :=
  measure_lt_top μ _

/-- Every normalized one-site factor is a probability law. Its positive mass comes from the cube. -/
theorem isProbabilityMeasure_finite_threshold_mask_factor {I : Type*} [Fintype I]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (T : ℝ) (hT : 0 < T) (b : I → Bool)
    (hC : 0 < (Measure.pi (fun _ : I => μ))
      (finiteThresholdMaskCube T b)) (i : I) :
    IsProbabilityMeasure
      ((μ {y : ℝ | if b i then y < -T else -T ≤ y})⁻¹ •
        μ.restrict {y : ℝ | if b i then y < -T else -T ≤ y}) := by
  constructor
  rw [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel
    (finite_threshold_mask_factor_mass_pos μ T hT b hC i).ne' (measure_ne_top μ _)

/-- The normalized cube restriction has total mass one. -/
theorem isProbabilityMeasure_finite_threshold_mask_normalized {I : Type*} [Fintype I]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (T : ℝ) (_hT : 0 < T) (b : I → Bool)
    (hC : 0 < (Measure.pi (fun _ : I => μ))
      (finiteThresholdMaskCube T b)) :
    IsProbabilityMeasure
      (((Measure.pi (fun _ : I => μ))
          (finiteThresholdMaskCube T b))⁻¹ •
        (Measure.pi (fun _ : I => μ)).restrict
          (finiteThresholdMaskCube T b)) := by
  constructor
  rw [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hC.ne' (measure_ne_top _ _)

/-- Normalizing a cube of positive mass gives the product of the normalized one-site half-lines. -/
theorem finite_threshold_mask_normalized_eq_pi {I : Type*} [Fintype I]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (T : ℝ) (hT : 0 < T) (b : I → Bool)
    (hC : 0 < (Measure.pi (fun _ : I => μ))
      (finiteThresholdMaskCube T b)) :
    ((Measure.pi (fun _ : I => μ))
        (finiteThresholdMaskCube T b))⁻¹ •
      (Measure.pi (fun _ : I => μ)).restrict
        (finiteThresholdMaskCube T b) =
      Measure.pi (fun i =>
        (μ {y : ℝ | if b i then y < -T else -T ≤ y})⁻¹ •
          μ.restrict {y : ℝ | if b i then y < -T else -T ≤ y}) := by
  have (i : I) := isProbabilityMeasure_finite_threshold_mask_factor μ T hT b hC i
  rw [finite_threshold_mask_cube_measure μ T hT b,
    finite_threshold_mask_cube_restrict μ T hT b]
  refine (Measure.pi_eq fun s _hs => ?_).symm
  rw [Measure.smul_apply, smul_eq_mul, Measure.pi_pi,
    ENNReal.prod_inv_distrib (fun _ _ j _ _ => Or.inr (measure_ne_top μ _)),
    ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => by rw [Measure.smul_apply, smul_eq_mul]

/-- A one-site factor of mass zero makes the cube null, so no conditional law is assigned to it. -/
theorem finite_threshold_mask_cube_measure_zero_of_factor_zero {I : Type*} [Fintype I]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (T : ℝ) (hT : 0 < T) (b : I → Bool)
    (i : I) (hi : μ {y : ℝ | if b i then y < -T else -T ≤ y} = 0) :
    (Measure.pi (fun _ : I => μ))
      (finiteThresholdMaskCube T b) = 0 := by
  rw [finite_threshold_mask_cube_measure μ T hT b]
  exact Finset.prod_eq_zero (Finset.mem_univ i) hi

end LPPDifferentiability
