/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Probability.EnvironmentResample
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Resampling below the horizontal axis

A splice that keeps one canonical environment at nonnegative heights and takes the
other environment below height zero still has the canonical law. This is the first
coupling step in the public Strong existence proof.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace LPPDifferentiability

/-- The literal half-plane splice is measurable, by checking each output coordinate.
This is the coupling construction used in the public Strong existence proof at
`Strong Existence_final.tex`, lines 985–987. -/
theorem measurable_horizontal_halfPlane_resample :
    Measurable (fun p : Environment × Environment => fun z : Lattice =>
      if 0 ≤ z.2 then p.1 z else p.2 z) := by
  classical
  apply Measurable.of_eval
  intro z
  by_cases hz : 0 ≤ z.2
  · have hform :
        (fun p : Environment × Environment => if 0 ≤ z.2 then p.1 z else p.2 z) =
          fun p => p.1 z := by
      funext p
      simp [hz]
    rw [hform]
    simpa only [Function.comp_def] using
      (measurable_environment_eval z).comp
        (measurable_fst : Measurable
          (Prod.fst : Environment × Environment → Environment))
  · have hform :
        (fun p : Environment × Environment => if 0 ≤ z.2 then p.1 z else p.2 z) =
          fun p => p.2 z := by
      funext p
      simp [hz]
    rw [hform]
    simpa only [Function.comp_def] using
      (measurable_environment_eval z).comp
        (measurable_snd : Measurable
          (Prod.snd : Environment × Environment → Environment))

/-- At every site of nonnegative height, the splice keeps the first environment,
as required by the coupling in the public Strong existence proof, lines 985–987. -/
theorem horizontal_halfPlane_resample_apply_nonneg
    (p : Environment × Environment) (z : Lattice) (hz : 0 ≤ z.2) :
    (fun pair : Environment × Environment => fun site : Lattice =>
      if 0 ≤ site.2 then pair.1 site else pair.2 site) p z = p.1 z := by
  simp [hz]

/-- The half-plane splice assigns the canonical product probability to every finite
box. This is the finite-cylinder calculation for the coupling in the public Strong
existence proof, lines 985–987. -/
theorem environmentLaw_map_horizontal_halfPlane_resample_box
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (s : Finset Lattice)
    (t : Lattice → Set ℝ) (ht : ∀ z, MeasurableSet (t z)) :
    ((environmentLaw μ).prod (environmentLaw μ)).map
      (fun p : Environment × Environment => fun z : Lattice =>
        if 0 ≤ z.2 then p.1 z else p.2 z)
      (Set.pi (↑s) t) = ∏ z ∈ s, μ (t z) := by
  classical
  -- Step 1: the map sends each tested coordinate to one of the two measurable inputs.
  have hsplice : Measurable (fun p : Environment × Environment => fun z : Lattice =>
      if 0 ≤ z.2 then p.1 z else p.2 z) :=
    measurable_horizontal_halfPlane_resample
  have hbox : MeasurableSet (Set.pi (↑s) t) :=
    MeasurableSet.pi s.countable_toSet (fun z _ => ht z)
  rw [Measure.map_apply hsplice hbox]

  -- Step 2: split the finite set of tested sites by the sign of their height.
  let upper : Finset Lattice := s.filter (fun z => 0 ≤ z.2)
  have hpre :
      (fun p : Environment × Environment => fun z : Lattice =>
        if 0 ≤ z.2 then p.1 z else p.2 z) ⁻¹' Set.pi (↑s) t =
        Set.pi (↑upper) t ×ˢ Set.pi (↑(s \ upper)) t := by
    ext p
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod,
      Finset.mem_sdiff]
    constructor
    · intro hp
      constructor
      · intro z hz
        have hz' : z ∈ s ∧ 0 ≤ z.2 := Finset.mem_filter.mp hz
        have hvalue : (if 0 ≤ z.2 then p.1 z else p.2 z) ∈ t z := hp z hz'.1
        simpa [hz'.2] using hvalue
      · intro z hz
        have hnegative : ¬ 0 ≤ z.2 := by
          intro hpositive
          exact hz.2 (Finset.mem_filter.mpr ⟨hz.1, hpositive⟩)
        have hvalue : (if 0 ≤ z.2 then p.1 z else p.2 z) ∈ t z := hp z hz.1
        simpa [hnegative] using hvalue
    · rintro ⟨hupper, hlower⟩ z hz
      by_cases hpositive : 0 ≤ z.2
      · have hzUpper : z ∈ upper := Finset.mem_filter.mpr ⟨hz, hpositive⟩
        have hvalue : p.1 z ∈ t z := hupper z hzUpper
        simpa [hpositive] using hvalue
      · have hzNotUpper : z ∉ upper := by
          intro hzUpper
          have hzUpper' : z ∈ s ∧ 0 ≤ z.2 := Finset.mem_filter.mp hzUpper
          exact hpositive hzUpper'.2
        have hvalue : p.2 z ∈ t z := hlower z ⟨hz, hzNotUpper⟩
        simpa [hpositive] using hvalue

  -- Step 3: independence of the two input environments makes the preimage probability a product.
  rw [hpre, Measure.prod_prod]
  change
    Measure.infinitePi (fun _ : Lattice => μ) (Set.pi (↑upper) t) *
      Measure.infinitePi (fun _ : Lattice => μ) (Set.pi (↑(s \ upper)) t) =
        ∏ z ∈ s, μ (t z)
  rw [Measure.infinitePi_pi _ (fun z _ => ht z),
    Measure.infinitePi_pi _ (fun z _ => ht z)]

  -- Step 4: the two finite products partition the product over all tested sites.
  have hupperSubset : upper ⊆ s := Finset.filter_subset _ _
  have hupperInter : s ∩ upper = upper := Finset.inter_eq_right.mpr hupperSubset
  calc
    (∏ z ∈ upper, μ (t z)) * ∏ z ∈ s \ upper, μ (t z) =
        (∏ z ∈ s ∩ upper, μ (t z)) * ∏ z ∈ s \ upper, μ (t z) := by
          rw [hupperInter]
    _ = ∏ z ∈ s, μ (t z) :=
      Finset.prod_inter_mul_prod_sdiff s upper (fun z => μ (t z))

/-- Mixing two independent canonical environments below the horizontal axis
preserves the canonical environment law. This is the marginal coupling step in the
public Strong existence proof, `Strong Existence_final.tex`, lines 985–987. -/
theorem environmentLaw_map_horizontal_halfPlane_resample
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ((environmentLaw μ).prod (environmentLaw μ)).map
      (fun p : Environment × Environment =>
        fun z : Lattice => if 0 ≤ z.2 then p.1 z else p.2 z) =
      environmentLaw μ := by
  change _ = Measure.infinitePi (fun _ : Lattice => μ)
  apply Measure.eq_infinitePi
  intro s t ht
  exact environmentLaw_map_horizontal_halfPlane_resample_box μ s t ht

end LPPDifferentiability
