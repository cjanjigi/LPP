/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.FiniteMaskConditionalLaw
public import Mathlib.Probability.Independence.Basic

/-!
# Coordinate laws under a normalized finite threshold cube

This file gives the one-coordinate laws and the laws of selected coordinates under the product
measure restricted to a threshold cube and normalized. The coordinates are independent under
this normalized law. Injectivity of the selection map says that the selected sites are distinct.
-/

public section

open MeasureTheory ProbabilityTheory

namespace LPPDifferentiability

/-- Each coordinate has the normalized one-site law: `μ` restricted to its half-line (below `-T`
or at least `-T`, as the mask says), divided by the mass of that half-line. -/
theorem finite_threshold_mask_normalized_marginal {I : Type*} [Fintype I]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (T : ℝ) (hT : 0 < T) (b : I → Bool)
    (hC : 0 < (Measure.pi (fun _ : I => μ))
      (finiteThresholdMaskCube T b)) (i : I) :
    (((Measure.pi (fun _ : I => μ))
        (finiteThresholdMaskCube T b))⁻¹ •
      (Measure.pi (fun _ : I => μ)).restrict
        (finiteThresholdMaskCube T b)).map
          (fun x : I → ℝ => x i) =
      (μ {y : ℝ | if b i then y < -T else -T ≤ y})⁻¹ •
        μ.restrict {y : ℝ | if b i then y < -T else -T ≤ y} := by
  have (j : I) := isProbabilityMeasure_finite_threshold_mask_factor μ T hT b hC j
  rw [finite_threshold_mask_normalized_eq_pi μ T hT b hC]
  exact (measurePreserving_eval _ i).map_eq

/-- The coordinate projections are independent under the normalized cube law. -/
theorem finite_threshold_mask_normalized_iIndepFun {I : Type*} [Fintype I]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (T : ℝ) (hT : 0 < T) (b : I → Bool)
    (hC : 0 < (Measure.pi (fun _ : I => μ))
      (finiteThresholdMaskCube T b)) :
    iIndepFun (fun i (x : I → ℝ) => x i)
      (((Measure.pi (fun _ : I => μ))
          (finiteThresholdMaskCube T b))⁻¹ •
        (Measure.pi (fun _ : I => μ)).restrict
          (finiteThresholdMaskCube T b)) := by
  have (j : I) := isProbabilityMeasure_finite_threshold_mask_factor μ T hT b hC j
  rw [finite_threshold_mask_normalized_eq_pi μ T hT b hC]
  exact iIndepFun_pi (fun _ => measurable_id.aemeasurable)

/-- Selecting finitely many distinct coordinates gives the product of their one-site laws. -/
theorem finite_threshold_mask_normalized_selected_map_pi
    {I J : Type*} [Fintype I] [Fintype J]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (T : ℝ) (hT : 0 < T) (b : I → Bool)
    (hC : 0 < (Measure.pi (fun _ : I => μ))
      (finiteThresholdMaskCube T b))
    (f : J → I) (hf : Function.Injective f) :
    (((Measure.pi (fun _ : I => μ))
        (finiteThresholdMaskCube T b))⁻¹ •
      (Measure.pi (fun _ : I => μ)).restrict
        (finiteThresholdMaskCube T b)).map
          (fun x : I → ℝ => fun j => x (f j)) =
      Measure.pi (fun j =>
        (μ {y : ℝ | if b (f j) then y < -T else -T ≤ y})⁻¹ •
          μ.restrict {y : ℝ | if b (f j) then y < -T else -T ≤ y}) := by
  have hindep := (finite_threshold_mask_normalized_iIndepFun μ T hT b hC).precomp hf
  rw [hindep.map_fun_eq_pi_map
    (fun j => (measurable_pi_apply (f j)).aemeasurable)]
  congr 1
  funext j
  exact finite_threshold_mask_normalized_marginal μ T hT b hC (f j)

/-- Distinct selected coordinates that are all good (not below `-T`) have the product of the
conditional law on `[-T, ∞)`. -/
theorem finite_threshold_mask_normalized_good_selected_map_pi
    {I J : Type*} [Fintype I] [Fintype J]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (T : ℝ) (hT : 0 < T) (b : I → Bool)
    (hC : 0 < (Measure.pi (fun _ : I => μ))
      (finiteThresholdMaskCube T b))
    (f : J → I) (hf : Function.Injective f) (hgood : ∀ j, b (f j) = false) :
    (((Measure.pi (fun _ : I => μ))
        (finiteThresholdMaskCube T b))⁻¹ •
      (Measure.pi (fun _ : I => μ)).restrict
        (finiteThresholdMaskCube T b)).map
          (fun x : I → ℝ => fun j => x (f j)) =
      Measure.pi (fun _ : J =>
        (μ (Set.Ici (-T)))⁻¹ • μ.restrict (Set.Ici (-T))) := by
  rw [finite_threshold_mask_normalized_selected_map_pi μ T hT b hC f hf]
  congr 1
  funext j
  simp only [hgood j, Bool.false_eq_true, ↓reduceIte]
  rfl

end LPPDifferentiability
