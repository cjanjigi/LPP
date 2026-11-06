/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Probability.DisjointSupport
public import LPP_Foundations.Probability.Stationarity
public import LPP_Foundations.Model.Translations
public import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-! Finite-coordinate events become independent of sufficiently distant translates. -/

public section

open MeasureTheory Set ProbabilityTheory

namespace LPPDifferentiability

/-- The coordinate translation preserves the iid environment law. -/
theorem measurePreserving_environment_translation (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (v : Lattice) :
    MeasurePreserving (fun ω : Environment => fun z => ω (v + z))
      (environmentLaw μ) (environmentLaw μ) :=
  ⟨measurable_pi_iff.mpr (fun z => measurable_environment_eval (v + z)),
    environmentLaw_map_translation μ v⟩

/-- A finite-coordinate event is independent of its translate when the two sets of
coordinates are disjoint. -/
theorem environmentLaw_cylinder_inter_translation (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (S : Finset Lattice) (v : Lattice) (hS : Disjoint S (S.image fun z => v + z))
    (B : Set ({z : Lattice // z ∈ S} → ℝ)) (hB : MeasurableSet B) :
    environmentLaw μ
      ({ω : Environment | (fun z : {z : Lattice // z ∈ S} => ω z.val) ∈ B} ∩
        (fun ω : Environment => fun z => ω (v + z)) ⁻¹'
          {ω : Environment | (fun z : {z : Lattice // z ∈ S} => ω z.val) ∈ B}) =
      environmentLaw μ {ω : Environment | (fun z : {z : Lattice // z ∈ S} => ω z.val) ∈ B} *
      environmentLaw μ {ω : Environment | (fun z : {z : Lattice // z ∈ S} => ω z.val) ∈ B} := by
  classical
  let T := S.image fun z => v + z
  let r : ({z : Lattice // z ∈ T} → ℝ) → ({z : Lattice // z ∈ S} → ℝ) :=
    fun x z => x ⟨v + z.val, Finset.mem_image.mpr ⟨z.val, z.property, rfl⟩⟩
  have hr : Measurable r :=
    measurable_pi_iff.mpr fun z => measurable_pi_apply _
  have hind := (indepFun_environment_restrict μ S T hS).comp measurable_id hr
  have h := hind.measure_inter_preimage_eq_mul B B hB hB
  have hm := (measurePreserving_environment_translation μ v).measure_preimage
    ((hB.preimage (measurable_environment_restrict S)).nullMeasurableSet)
  let C : Set Environment := {ω | (fun z : {z : Lattice // z ∈ S} => ω z.val) ∈ B}
  change environmentLaw μ (C ∩ (fun ω : Environment => fun z => ω (v + z)) ⁻¹' C) =
    environmentLaw μ C *
      environmentLaw μ ((fun ω : Environment => fun z => ω (v + z)) ⁻¹' C) at h
  change environmentLaw μ ((fun ω : Environment => fun z => ω (v + z)) ⁻¹' C) =
    environmentLaw μ C at hm
  rw [hm] at h
  exact h

/-- Along a nonzero lattice direction, every finite-coordinate event has exactly
product probability with all sufficiently distant iterates of itself. -/
theorem eventually_environmentLaw_cylinder_inter_iterate (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (v : Lattice) (hv : v ≠ 0) (S : Finset Lattice)
    (B : Set ({z : Lattice // z ∈ S} → ℝ)) (hB : MeasurableSet B) :
    ∀ᶠ n : ℕ in Filter.atTop,
      environmentLaw μ
        ({ω : Environment | (fun z : {z : Lattice // z ∈ S} => ω z.val) ∈ B} ∩
          (fun ω : Environment => fun z => ω (v + z))^[n] ⁻¹'
            {ω : Environment | (fun z : {z : Lattice // z ∈ S} => ω z.val) ∈ B}) =
        environmentLaw μ {ω : Environment | (fun z : {z : Lattice // z ∈ S} => ω z.val) ∈ B} *
        environmentLaw μ {ω : Environment | (fun z : {z : Lattice // z ∈ S} => ω z.val) ∈ B} := by
  filter_upwards [eventually_disjoint_finite_translates v hv S S] with n hn
  have heq : (fun ω : Environment => fun z => ω (v + z))^[n] =
      (fun ω : Environment => fun z => ω (n • v + z)) := by
    funext ω z
    exact environment_translate_iterate ω v n z
  rw [heq]
  exact environmentLaw_cylinder_inter_translation μ S (n • v) hn B hB

end LPPDifferentiability
