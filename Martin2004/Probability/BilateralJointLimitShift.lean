/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.BilateralJointShift
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Basic

/-!
# Shift invariance of bilateral joint limits

Weak limits of finite bilateral joint laws retain their joint shift
invariance. The array marginal is also retained in the limit.
-/

public section

open MeasureTheory Filter Topology BoundedContinuousFunction

namespace LPPDifferentiability

/-- A weak limit of the actual finite joint laws is preserved by the literal
joint shift, under the actual array-law invariance premise. -/
theorem measurePreserving_bilateralJointShift_of_tendsto_uniformBilateralJointLaw
    (ρ : ProbabilityMeasure BilateralArray)
    (hρ : MeasurePreserving bilateralArrayShift (ρ : Measure BilateralArray)
      (ρ : Measure BilateralArray))
    (ν : ProbabilityMeasure BilateralJoint) (r : ℕ → ℕ) (hr : StrictMono r)
    (hν : Tendsto (fun i => uniformBilateralJointLaw ρ (r i)) atTop (𝓝 ν)) :
    MeasurePreserving bilateralJointShift (ν : Measure BilateralJoint)
      (ν : Measure BilateralJoint) := by
  have hmapped := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun i => uniformBilateralJointLaw ρ (r i)) ν hν continuous_bilateralJointShift
  refine ⟨measurable_bilateralJointShift, ?_⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  have hl := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hmapped f).sub
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hν f)
  have hz : Tendsto
      (fun i => (∫ p, f (bilateralJointShift p)
          ∂(uniformBilateralJointLaw ρ (r i) : Measure BilateralJoint)) -
        (∫ p, f p ∂(uniformBilateralJointLaw ρ (r i) : Measure BilateralJoint)))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun i =>
      norm_integral_uniformBilateralJointLaw_shift_sub_le ρ hρ (r i) f)
    have hd : Tendsto (fun n : ℕ => 2 * ‖f‖ / (n + 1 : ℝ)) atTop (𝓝 0) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (tendsto_add_atTop_iff_nat 1).2
          (tendsto_const_div_atTop_nhds_zero_nat (2 * ‖f‖))
    exact hd.comp hr.tendsto_atTop
  have hl' : Tendsto
      (fun i => (∫ p, f (bilateralJointShift p)
          ∂(uniformBilateralJointLaw ρ (r i) : Measure BilateralJoint)) -
        (∫ p, f p ∂(uniformBilateralJointLaw ρ (r i) : Measure BilateralJoint)))
      atTop (𝓝 ((∫ p, f p ∂((ν : Measure BilateralJoint).map bilateralJointShift)) -
        (∫ p, f p ∂(ν : Measure BilateralJoint)))) := by
    convert hl using 1
    funext i
    rw [ProbabilityMeasure.toMeasure_map,
      integral_map measurable_bilateralJointShift.aemeasurable
        f.continuous.measurable.aestronglyMeasurable]
    simp only [ProbabilityMeasure.toMeasure_map]
  exact sub_eq_zero.mp (tendsto_nhds_unique hl' hz)

/-- The same weak limit retains the actual array marginal of every finite law. -/
theorem measurePreserving_fst_of_tendsto_uniformBilateralJointLaw
    (ρ : ProbabilityMeasure BilateralArray) (ν : ProbabilityMeasure BilateralJoint)
    (r : ℕ → ℕ) (_ : StrictMono r)
    (hν : Tendsto (fun i => uniformBilateralJointLaw ρ (r i)) atTop (𝓝 ν)) :
    MeasurePreserving Prod.fst (ν : Measure BilateralJoint)
      (ρ : Measure BilateralArray) := by
  have hmapped := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun i => uniformBilateralJointLaw ρ (r i)) ν hν continuous_fst
  refine ⟨measurable_fst, ?_⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  have hl := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hmapped f
  have hconst : Tendsto (fun _ : ℕ => ∫ x, f x ∂(ρ : Measure BilateralArray))
      atTop (𝓝 (∫ x, f x ∂(ρ : Measure BilateralArray))) := tendsto_const_nhds
  have hl' : Tendsto
      (fun i => (∫ p, f (Prod.fst p)
          ∂(uniformBilateralJointLaw ρ (r i) : Measure BilateralJoint)) -
        (∫ x, f x ∂(ρ : Measure BilateralArray)))
      atTop (𝓝 ((∫ p, f p ∂((ν : Measure BilateralJoint).map Prod.fst)) -
        (∫ x, f x ∂(ρ : Measure BilateralArray)))) := by
    convert hl.sub hconst using 1
    funext i
    rw [ProbabilityMeasure.toMeasure_map,
      integral_map measurable_fst.aemeasurable
        f.continuous.measurable.aestronglyMeasurable]
    simp only [ProbabilityMeasure.toMeasure_map]
  have hz : Tendsto
      (fun i => (∫ p, f (Prod.fst p)
          ∂(uniformBilateralJointLaw ρ (r i) : Measure BilateralJoint)) -
        (∫ x, f x ∂(ρ : Measure BilateralArray)))
      atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards with i
    have hfst := uniformBilateralJointLaw_fst ρ (r i)
    rw [← integral_map measurable_fst.aemeasurable
      f.continuous.measurable.aestronglyMeasurable, hfst.map_eq]
    simp only [sub_self]
  exact sub_eq_zero.mp (tendsto_nhds_unique hl' hz)

end LPPDifferentiability
