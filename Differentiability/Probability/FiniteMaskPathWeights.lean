/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.ConditionalFinitePathWeights
public import Differentiability.Probability.FiniteMaskConditionalCoordinates

/-!
# A fixed selected path under a finite mask cube

This file transfers the failure estimate for a fixed selected path to the normalized law of a
finite mask cube. The selected sites are good, so their values are at least `-T`.
-/

public section

open MeasureTheory
open scoped BigOperators ENNReal

namespace LPPDifferentiability

/-- For fixed distinct good coordinates, under a mask cube of positive mass, the failure
probability under the normalized restriction law obeys the estimate of
`conditional_finite_weight_failure_le`. -/
theorem finite_mask_selected_weight_failure_le
    {I : Type*} [Fintype I]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (T p b t : ℝ)
    (hp : 1 < p) (hT : 0 < T)
    (hthreshold : (2 : ℝ≥0∞)⁻¹ ≤ μ (Set.Ici (-T))) (hb : 0 < b) (ht : 0 < t)
    (hmoment : (∫⁻ x, ENNReal.ofReal ((max (-x) 0) ^ p) ∂μ) < ∞)
    (mask : I → Bool)
    (hC : 0 < (Measure.pi (fun _ : I => μ))
      {x | ∀ i, if mask i then x i < -T else -T ≤ x i})
    (m n K : ℕ) (hmn : m ≤ n) (hK : 1 ≤ K)
    (f : Fin m → I) (hf : Function.Injective f) (hgood : ∀ j, mask (f j) = false) :
    (((Measure.pi (fun _ : I => μ))
      {x | ∀ i, if mask i then x i < -T else -T ≤ x i})⁻¹ •
        (Measure.pi (fun _ : I => μ)).restrict
          {x | ∀ i, if mask i then x i < -T else -T ≤ x i}).real
      {x | (∑ j, x (f j)) < -2 * (∫ y, max (-y) 0 ∂μ) * m - (K - 1 : ℕ) * T - t} ≤
      (2 * n * (∫ y, (max (-y) 0) ^ p ∂μ) * b ^ (-p)) ^ K +
        Real.exp (-t ^ 2 / (2 * b * (2 * (∫ y, max (-y) 0 ∂μ) * n + t / 3))) := by
  have hmap := finite_threshold_mask_normalized_good_selected_map_pi μ T hT mask hC f hf hgood
  have hmeas : Measurable (fun x : I → ℝ => fun j => x (f j)) :=
    measurable_pi_iff.mpr fun j => measurable_pi_apply (f j)
  have hfail : MeasurableSet {x : Fin m → ℝ | (∑ j, x j) <
      -2 * (∫ y, max (-y) 0 ∂μ) * m - (K - 1 : ℕ) * T - t} :=
    measurableSet_lt (Finset.measurable_sum _ fun j _ => measurable_pi_apply j) measurable_const
  have h := conditional_finite_weight_failure_le μ T p b t hp hT hthreshold hb ht hmoment m n K hmn hK
  rw [← hmap, map_measureReal_apply hmeas hfail] at h
  exact h

/-- Undo the normalization, using the (positive) mass of the cube. -/
theorem finite_mask_restriction_real_eq_mass_mul
    {I : Type*} [Fintype I]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (T : ℝ) (mask : I → Bool)
    (hC : 0 < (Measure.pi (fun _ : I => μ))
      {x | ∀ i, if mask i then x i < -T else -T ≤ x i}) (E : Set (I → ℝ)) :
    ((Measure.pi (fun _ : I => μ)).restrict
      {x | ∀ i, if mask i then x i < -T else -T ≤ x i}).real E =
    (Measure.pi (fun _ : I => μ)).real
      {x | ∀ i, if mask i then x i < -T else -T ≤ x i} *
      (((Measure.pi (fun _ : I => μ))
        {x | ∀ i, if mask i then x i < -T else -T ≤ x i})⁻¹ •
        (Measure.pi (fun _ : I => μ)).restrict
          {x | ∀ i, if mask i then x i < -T else -T ≤ x i}).real E := by
  let P := Measure.pi (fun _ : I => μ)
  let C := {x : I → ℝ | ∀ i, if mask i then x i < -T else -T ≤ x i}
  change (P.restrict C).real E = P.real C * ((P C)⁻¹ • P.restrict C).real E
  rw [measureReal_ennreal_smul_apply, ENNReal.toReal_inv]
  have hpos : 0 < (P C).toReal := ENNReal.toReal_pos hC.ne' (measure_ne_top P C)
  exact (mul_inv_cancel_left₀ hpos.ne' _).symm

/-- The threshold cube is the preimage of the Boolean mask under the threshold-indicator map. -/
theorem finite_threshold_cube_eq_mask_fiber
    {I : Type*} (T : ℝ) (mask : I → Bool) :
    {x : I → ℝ | ∀ i, if mask i then x i < -T else -T ≤ x i} =
      (fun x : I → ℝ => fun i => if x i < -T then true else false) ⁻¹' {mask} := by
  ext x
  constructor
  · intro hx
    apply funext
    intro i
    have hi := hx i
    cases h : mask i <;> simp_all
  · intro hx i
    have hi := congrFun hx i
    cases h : mask i <;> simp_all

end LPPDifferentiability
