/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Probability.EnvironmentLaw
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Measure.MeasuredSets

/-!
# Finite-coordinate approximation of canonical environment events

Finite-coordinate measurable cylinders form a ring of sets that generates the product sigma
algebra. The standard approximation criterion for a generating ring then approximates every
measurable event, in the probability of the symmetric difference, by a cylinder event.
-/

public section

open MeasureTheory Set
open scoped ENNReal symmDiff

namespace LPPDifferentiability

/-- Restricting an environment to finitely many coordinates is measurable. -/
private theorem measurable_environment_restrict_aux (S : Finset Lattice) :
    Measurable (fun ω : Environment => fun z : {z : Lattice // z ∈ S} => ω z.val) :=
  measurable_pi_iff.mpr fun z => measurable_pi_apply z.val

/-- A measurable finite-vector event pulls back to a measurable environment event. -/
theorem measurableSet_environment_restrict (S : Finset Lattice)
    {B : Set ({z : Lattice // z ∈ S} → ℝ)} (hB : MeasurableSet B) :
    MeasurableSet {ω : Environment | (fun z : {z : Lattice // z ∈ S} => ω z.val) ∈ B} :=
  (measurable_environment_restrict_aux S) hB

/-- Every measurable canonical event can be approximated by a measurable event
on a finite vector of its coordinates, with arbitrarily small probability error. -/
theorem exists_finite_coordinate_approx (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {A : Set Environment} (hA : MeasurableSet A) {ε : ℝ} (hε : 0 < ε) :
    ∃ (S : Finset Lattice) (B : Set ({z : Lattice // z ∈ S} → ℝ)),
      MeasurableSet B ∧
      environmentLaw μ
        (A ∆ {ω : Environment | (fun z : {z : Lattice // z ∈ S} => ω z.val) ∈ B}) <
        ENNReal.ofReal ε := by
  have hcover : ∃ D : Set (Set Environment), D.Countable ∧
      D ⊆ measurableCylinders (fun _ : Lattice => ℝ) ∧ environmentLaw μ (⋃₀ D)ᶜ = 0 := by
    refine ⟨{univ}, countable_singleton _, ?_, ?_⟩
    · exact singleton_subset_iff.mpr (univ_mem_measurableCylinders _)
    · simp only [sUnion_singleton, compl_univ, measure_empty]
  obtain ⟨C, hC, herror⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing
    (μ := environmentLaw μ) isSetRing_measurableCylinders hcover
    generateFrom_measurableCylinders.symm hA (ENNReal.ofReal_pos.mpr hε)
  obtain ⟨S, B, hB, rfl⟩ := (mem_measurableCylinders C).mp hC
  refine ⟨S, B, hB, ?_⟩
  rw [symmDiff_comm] at herror
  exact herror

end LPPDifferentiability
