/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.BilateralJointLaw
import ProbabilityBasics.Probability.UniformIncrementShift
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Tactic.Linarith

/-! Whole-carrier joint shift and the stationarity error of the actual finite laws. -/

@[expose] public section

open MeasureTheory BoundedContinuousFunction

namespace LPPDifferentiability

/-- Shift the original array and the bilateral increment sequence together. -/
def bilateralJointShift (p : BilateralJoint) : BilateralJoint :=
  (bilateralArrayShift p.1, fun t => p.2 (t + 1))

def bilateralJointUnshift (p : BilateralJoint) : BilateralJoint :=
  (bilateralArrayUnshift p.1, fun t => p.2 (t - 1))

theorem bilateralJointUnshift_shift (p : BilateralJoint) :
    bilateralJointUnshift (bilateralJointShift p) = p := by
  apply Prod.ext
  · exact bilateralArrayUnshift_shift p.1
  · funext t
    change p.2 (t - 1 + 1) = p.2 t
    rw [sub_add_cancel]

theorem bilateralJointShift_unshift (p : BilateralJoint) :
    bilateralJointShift (bilateralJointUnshift p) = p := by
  apply Prod.ext
  · exact bilateralArrayShift_unshift p.1
  · funext t
    change p.2 (t + 1 - 1) = p.2 t
    rw [add_sub_cancel_right]

theorem continuous_bilateralJointShift : Continuous bilateralJointShift :=
  (continuous_bilateralArrayShift.comp continuous_fst).prodMk
    (continuous_pi fun t => (continuous_apply (t + 1)).comp continuous_snd)

theorem continuous_bilateralJointUnshift : Continuous bilateralJointUnshift :=
  (continuous_bilateralArrayUnshift.comp continuous_fst).prodMk
    (continuous_pi fun t => (continuous_apply (t - 1)).comp continuous_snd)

theorem measurable_bilateralJointShift : Measurable bilateralJointShift :=
  (measurable_bilateralArrayShift.comp measurable_fst).prodMk
    (Measurable.of_eval fun t => (measurable_pi_apply (t + 1)).comp measurable_snd)

theorem measurable_bilateralJointUnshift : Measurable bilateralJointUnshift :=
  (measurable_bilateralArrayUnshift.comp measurable_fst).prodMk
    (Measurable.of_eval fun t => (measurable_pi_apply (t - 1)).comp measurable_snd)

/-- The literal shift is a homeomorphism on the entire joint carrier. -/
def bilateralJointShiftHomeomorph : BilateralJoint ≃ₜ BilateralJoint where
  toFun := bilateralJointShift
  invFun := bilateralJointUnshift
  left_inv := bilateralJointUnshift_shift
  right_inv := bilateralJointShift_unshift
  continuous_toFun := continuous_bilateralJointShift
  continuous_invFun := continuous_bilateralJointUnshift

def bilateralJointShiftMeasurableEquiv : BilateralJoint ≃ᵐ BilateralJoint where
  toEquiv := bilateralJointShiftHomeomorph.toEquiv
  measurable_toFun := measurable_bilateralJointShift
  measurable_invFun := measurable_bilateralJointUnshift

/-- Covariance, retaining the original array in the same graph. -/
theorem bilateralJointShift_graph (n : ℕ) (x : BilateralArray) :
    bilateralJointShift (bilateralJointGraph n x) =
      bilateralJointGraph (n + 1) (bilateralArrayShift x) := by
  apply Prod.ext
  · rfl
  · funext t
    exact (bilateralArrayIncrements_shift n x t).symm

/-- Joint graph laws advance by one under the actual invariant array law. -/
theorem bilateralJointLaw_shift (ρ : ProbabilityMeasure BilateralArray)
    (hρ : MeasurePreserving bilateralArrayShift (ρ : Measure BilateralArray)
      (ρ : Measure BilateralArray)) (n : ℕ) :
    (bilateralJointLaw ρ n : Measure BilateralJoint).map bilateralJointShift =
      (bilateralJointLaw ρ (n + 1) : Measure BilateralJoint) := by
  rw [bilateralJointLaw_toMeasure,
    Measure.map_map measurable_bilateralJointShift (measurable_bilateralJointGraph n)]
  have he : bilateralJointShift ∘ bilateralJointGraph n =
      bilateralJointGraph (n + 1) ∘ bilateralArrayShift :=
    funext (bilateralJointShift_graph n)
  rw [he, ← Measure.map_map (measurable_bilateralJointGraph (n + 1))
    measurable_bilateralArrayShift, hρ.map_eq]
  rfl

/-- Exact endpoint cancellation for the actual correlated joint mixture. -/
theorem integral_uniformBilateralJointLaw_shift_sub (ρ : ProbabilityMeasure BilateralArray)
    (hρ : MeasurePreserving bilateralArrayShift (ρ : Measure BilateralArray)
      (ρ : Measure BilateralArray)) (N : ℕ) (f : BilateralJoint →ᵇ ℝ) :
    (∫ p, f (bilateralJointShift p) ∂(uniformBilateralJointLaw ρ N : Measure BilateralJoint)) -
      (∫ p, f p ∂(uniformBilateralJointLaw ρ N : Measure BilateralJoint)) =
      ((∫ p, f p ∂(bilateralJointLaw ρ (N + 1) : Measure BilateralJoint)) -
        (∫ p, f p ∂(bilateralJointLaw ρ 0 : Measure BilateralJoint))) / (N + 1 : ℝ) := by
  let g := f.compContinuous ⟨bilateralJointShift, continuous_bilateralJointShift⟩
  change (∫ p, g p ∂_) - _ = _
  rw [integral_uniformBilateralJointLaw, integral_uniformBilateralJointLaw, ← sub_div]
  have hg (j : ℕ) :
      (∫ x, g (bilateralJointGraph j x) ∂(ρ : Measure BilateralArray)) =
        ∫ x, f (bilateralJointGraph (j + 1) x) ∂(ρ : Measure BilateralArray) := by
    rw [← integral_bilateralJointLaw ρ j g, ← integral_bilateralJointLaw ρ (j + 1) f,
      ← bilateralJointLaw_shift ρ hρ j,
      integral_map measurable_bilateralJointShift.aemeasurable
        f.continuous.measurable.aestronglyMeasurable]
    rfl
  simp_rw [hg]
  rw [sum_shift_sub (fun j => ∫ x, f (bilateralJointGraph j x)
    ∂(ρ : Measure BilateralArray)) (N + 1), integral_bilateralJointLaw,
    integral_bilateralJointLaw]

/-- Two bounded endpoints control stationarity error without moment assumptions. -/
theorem norm_integral_uniformBilateralJointLaw_shift_sub_le
    (ρ : ProbabilityMeasure BilateralArray)
    (hρ : MeasurePreserving bilateralArrayShift (ρ : Measure BilateralArray)
      (ρ : Measure BilateralArray)) (N : ℕ) (f : BilateralJoint →ᵇ ℝ) :
    ‖(∫ p, f (bilateralJointShift p) ∂(uniformBilateralJointLaw ρ N : Measure BilateralJoint)) -
      (∫ p, f p ∂(uniformBilateralJointLaw ρ N : Measure BilateralJoint))‖ ≤
      2 * ‖f‖ / (N + 1 : ℝ) := by
  rw [integral_uniformBilateralJointLaw_shift_sub ρ hρ, norm_div,
    Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ N + 1)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact (norm_sub_le _ _).trans (by
    linarith only [f.norm_integral_le_norm (bilateralJointLaw ρ (N + 1) : Measure BilateralJoint),
      f.norm_integral_le_norm (bilateralJointLaw ρ 0 : Measure BilateralJoint)])

end LPPDifferentiability
