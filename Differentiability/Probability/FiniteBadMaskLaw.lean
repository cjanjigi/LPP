/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Finite threshold-mask laws

This file gives the laws of a finite family of threshold indicators under a product probability
measure. For a fixed pattern of indicators (a Boolean mask), it gives the product formula for
its mass, and it shows that restricting the product measure to the pattern restricts each factor.
-/

public section

open MeasureTheory

namespace LPPDifferentiability

/-- The configurations with the indicated very bad sites at threshold `-T`.
The endpoint `-T` is on the good side, as in the conditional law for `lem:weights`. -/
@[expose] def finiteThresholdMaskCube {I : Type*} (T : ℝ) (b : I → Bool) : Set (I → ℝ) :=
  {x | ∀ i, if b i then x i < -T else -T ≤ x i}

/-- Membership in the cube is the indicated one-site test at every coordinate. -/
theorem mem_finiteThresholdMaskCube {I : Type*} (T : ℝ) (b : I → Bool) (x : I → ℝ) :
    x ∈ finiteThresholdMaskCube T b ↔ ∀ i, if b i then x i < -T else -T ≤ x i :=
  Iff.rfl

/-- A fixed threshold mask is the product of its one-site half-lines. -/
theorem finiteThresholdMaskCube_eq_pi {I : Type*} (T : ℝ) (b : I → Bool) :
    finiteThresholdMaskCube T b =
      Set.univ.pi (fun i => {y : ℝ | if b i then y < -T else -T ≤ y}) := by
  ext x
  simp [mem_finiteThresholdMaskCube]

/-- The configurations with a fixed finite threshold mask form a measurable rectangle. -/
theorem measurableSet_finite_threshold_mask_cube {I : Type*} [Fintype I]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (T : ℝ) (_hT : 0 < T) (b : I → Bool) :
    MeasurableSet (finiteThresholdMaskCube T b) := by
  rw [finiteThresholdMaskCube_eq_pi]
  exact MeasurableSet.univ_pi fun i => by
    by_cases hb : b i
    · simpa [hb] using
        (measurableSet_lt (measurable_id : Measurable fun y : ℝ => y) measurable_const)
    · simpa [hb] using
        (measurableSet_le measurable_const (measurable_id : Measurable fun y : ℝ => y))

/-- Restricting the finite product to one fixed threshold mask restricts each factor. -/
theorem finite_threshold_mask_cube_restrict {I : Type*} [Fintype I]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (T : ℝ) (_hT : 0 < T) (b : I → Bool) :
    (Measure.pi (fun _ : I => μ)).restrict (finiteThresholdMaskCube T b) =
      Measure.pi (fun i => μ.restrict {y : ℝ | if b i then y < -T else -T ≤ y}) := by
  rw [finiteThresholdMaskCube_eq_pi]
  exact Measure.restrict_pi_pi (fun _ : I => μ)
    (fun i => {y : ℝ | if b i then y < -T else -T ≤ y})

/-- The mass of a fixed threshold mask is the product of its coordinate masses. -/
theorem finite_threshold_mask_cube_measure {I : Type*} [Fintype I]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (T : ℝ) (_hT : 0 < T) (b : I → Bool) :
    (Measure.pi (fun _ : I => μ)) (finiteThresholdMaskCube T b) =
      ∏ i, μ {y : ℝ | if b i then y < -T else -T ≤ y} := by
  rw [finiteThresholdMaskCube_eq_pi]
  exact Measure.pi_pi (fun _ : I => μ)
    (fun i => {y : ℝ | if b i then y < -T else -T ≤ y})

/-- The coordinatewise threshold-indicator map is measurable. -/
theorem measurable_finite_threshold_mask {I : Type*} [Fintype I]
    (T : ℝ) :
    Measurable (fun x : I → ℝ => fun i => if x i < -T then true else false) := by
  have hcoord' : Measurable (fun y : ℝ => if y < -T then true else false) := by
    exact Measurable.ite (measurableSet_lt
      (measurable_id : Measurable fun y : ℝ => y) measurable_const)
      measurable_const measurable_const
  exact measurable_pi_iff.mpr fun i => hcoord'.comp (measurable_pi_apply i)

/-- The threshold-indicator vector has the product of its one-site Boolean marginals. -/
theorem finite_threshold_mask_map_pi {I : Type*} [Fintype I]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (T : ℝ) (_hT : 0 < T) :
    (Measure.pi (fun _ : I => μ)).map
        (fun x : I → ℝ => fun i => if x i < -T then true else false) =
      Measure.pi (fun _ : I => μ.map (fun y : ℝ => if y < -T then true else false)) := by
  have hcoord' : Measurable (fun y : ℝ => if y < -T then true else false) := by
    exact Measurable.ite (measurableSet_lt
      (measurable_id : Measurable fun y : ℝ => y) measurable_const)
      measurable_const measurable_const
  exact Measure.pi_map_pi (fun _ => hcoord'.aemeasurable)

/-- Every fixed Boolean mask has its exact product mass, including masks of mass zero. -/
theorem finite_threshold_mask_map_singleton {I : Type*} [Fintype I]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (T : ℝ) (hT : 0 < T) (b : I → Bool) :
    ((Measure.pi (fun _ : I => μ)).map
        (fun x : I → ℝ => fun i => if x i < -T then true else false)) {b} =
      ∏ i, μ {y : ℝ | if b i then y < -T else -T ≤ y} := by
  have hcoord : Measurable (fun y : ℝ => if y < -T then true else false) := by
    exact Measurable.ite (measurableSet_lt
      (measurable_id : Measurable fun y : ℝ => y) measurable_const)
      measurable_const measurable_const
  have hpre (c : Bool) :
      (fun y : ℝ => if y < -T then true else false) ⁻¹' {c} =
        {y : ℝ | if c then y < -T else -T ≤ y} := by
    ext y
    cases c <;> simp
  rw [finite_threshold_mask_map_pi μ T hT, Measure.pi_singleton]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Measure.map_apply_of_aemeasurable hcoord.aemeasurable
    (measurableSet_singleton (b i)), hpre (b i)]

end LPPDifferentiability
