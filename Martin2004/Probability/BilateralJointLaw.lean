/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.BilateralArrayIncrements
public import ProbabilityBasics.Probability.UniformOrigin
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-! Actual graph laws retaining the entire array and its auxiliary increments.
The natural parameter n represents positive root n+1; N represents N+1 roots. -/

@[expose] public section

open MeasureTheory BoundedContinuousFunction

namespace LPPDifferentiability

abbrev BilateralJoint := BilateralArray × (ℤ → ℝ)

/-- The literal graph of the auxiliary increments at root n+1. -/
def bilateralJointGraph (n : ℕ) (x : BilateralArray) : BilateralJoint :=
  (x, bilateralArrayIncrements n x)

theorem continuous_bilateralJointGraph (n : ℕ) : Continuous (bilateralJointGraph n) :=
  continuous_id.prodMk (continuous_bilateralArrayIncrements n)

theorem measurable_bilateralJointGraph (n : ℕ) : Measurable (bilateralJointGraph n) :=
  measurable_id.prodMk (measurable_bilateralArrayIncrements n)

/-- The actual joint graph law, with no replacement by independent marginals. -/
noncomputable def bilateralJointLaw (ρ : ProbabilityMeasure BilateralArray) (n : ℕ) :
    ProbabilityMeasure BilateralJoint :=
  ⟨(ρ : Measure BilateralArray).map (bilateralJointGraph n),
    (Measure.isProbabilityMeasure_map_iff
      (measurable_bilateralJointGraph n).aemeasurable).2 inferInstance⟩

/-- The existing finite uniform origin selects a graph while retaining x. -/
def uniformBilateralJointSampler (N : ℕ)
    (p : BilateralArray × Fin (N + 1)) : BilateralJoint :=
  bilateralJointGraph p.2.val p.1

theorem measurable_uniformBilateralJointSampler (N : ℕ) :
    Measurable (uniformBilateralJointSampler N) :=
  measurable_from_prod_countable_left fun u => measurable_bilateralJointGraph u.val

/-- The literal pushforward of the existing independent uniform-origin product. -/
noncomputable def uniformBilateralJointLaw (ρ : ProbabilityMeasure BilateralArray) (N : ℕ) :
    ProbabilityMeasure BilateralJoint :=
  ⟨(uniformOriginProduct (ρ : Measure BilateralArray) N).map
      (uniformBilateralJointSampler N),
    (Measure.isProbabilityMeasure_map_iff
      (measurable_uniformBilateralJointSampler N).aemeasurable).2 inferInstance⟩

theorem bilateralJointLaw_toMeasure (ρ : ProbabilityMeasure BilateralArray) (n : ℕ) :
    (bilateralJointLaw ρ n : Measure BilateralJoint) =
      (ρ : Measure BilateralArray).map (bilateralJointGraph n) := rfl

theorem uniformBilateralJointLaw_toMeasure (ρ : ProbabilityMeasure BilateralArray) (N : ℕ) :
    (uniformBilateralJointLaw ρ N : Measure BilateralJoint) =
      (uniformOriginProduct (ρ : Measure BilateralArray) N).map
        (uniformBilateralJointSampler N) := rfl

/-- The array marginal of every graph law is exactly the supplied law. -/
theorem bilateralJointLaw_fst (ρ : ProbabilityMeasure BilateralArray) (n : ℕ) :
    MeasurePreserving Prod.fst (bilateralJointLaw ρ n : Measure BilateralJoint)
      (ρ : Measure BilateralArray) := by
  refine ⟨measurable_fst, ?_⟩
  rw [bilateralJointLaw_toMeasure,
    Measure.map_map measurable_fst (measurable_bilateralJointGraph n)]
  exact Measure.map_id

/-- The array marginal is preserved by the actual finite mixture. -/
theorem uniformBilateralJointLaw_fst (ρ : ProbabilityMeasure BilateralArray) (N : ℕ) :
    MeasurePreserving Prod.fst (uniformBilateralJointLaw ρ N : Measure BilateralJoint)
      (ρ : Measure BilateralArray) := by
  refine ⟨measurable_fst, ?_⟩
  rw [uniformBilateralJointLaw_toMeasure,
    Measure.map_map measurable_fst (measurable_uniformBilateralJointSampler N)]
  exact (uniformOriginProduct_fst (ρ : Measure BilateralArray) N).map_eq

theorem integral_bilateralJointLaw (ρ : ProbabilityMeasure BilateralArray) (n : ℕ)
    (f : BilateralJoint →ᵇ ℝ) :
    (∫ p, f p ∂(bilateralJointLaw ρ n : Measure BilateralJoint)) =
      ∫ x, f (bilateralJointGraph n x) ∂(ρ : Measure BilateralArray) := by
  rw [bilateralJointLaw_toMeasure,
    integral_map (measurable_bilateralJointGraph n).aemeasurable
      f.continuous.measurable.aestronglyMeasurable]

/-- Exact averaging under the literal uniform-origin pushforward. -/
theorem integral_uniformBilateralJointLaw (ρ : ProbabilityMeasure BilateralArray) (N : ℕ)
    (f : BilateralJoint →ᵇ ℝ) :
    (∫ p, f p ∂(uniformBilateralJointLaw ρ N : Measure BilateralJoint)) =
      (∑ u : Fin (N + 1), ∫ x, f (bilateralJointGraph u.val x)
        ∂(ρ : Measure BilateralArray)) / (N + 1 : ℝ) := by
  rw [uniformBilateralJointLaw_toMeasure,
    integral_map (measurable_uniformBilateralJointSampler N).aemeasurable
      f.continuous.measurable.aestronglyMeasurable]
  apply integral_uniformOrigin_family (ρ : Measure BilateralArray) N
    (fun u x => f (bilateralJointGraph u.val x))
  · intro u
    exact f.continuous.measurable.comp (measurable_bilateralJointGraph u.val)
  · intro u
    exact (integrable_const ‖f‖).mono'
      (f.continuous.measurable.comp (measurable_bilateralJointGraph u.val)).aestronglyMeasurable
      (ae_of_all _ fun _ => f.norm_coe_le_norm _)

end LPPDifferentiability
