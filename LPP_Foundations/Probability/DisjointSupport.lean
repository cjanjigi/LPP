/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Probability.CoordinateLaw

/-!
Independence on disjoint finite sets of sites.

The sets of sites here are deterministic. The coordinate law may have atoms
and may give positive mass to negative real weights.
-/

public section

open MeasureTheory ProbabilityTheory

namespace LPPDifferentiability

/-- The vector of environment weights on a finite set of sites is measurable. -/
theorem measurable_environment_restrict (S : Finset Lattice) :
    Measurable (fun ω : Environment => fun s : {z : Lattice // z ∈ S} => ω s.val) :=
  Measurable.of_eval (fun s => measurable_environment_eval s.val)

/-- The coordinate vectors on two disjoint finite sets of sites are independent. -/
theorem indepFun_environment_restrict (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (S T : Finset Lattice) (hST : Disjoint S T) :
    IndepFun (fun ω : Environment => fun s : {z : Lattice // z ∈ S} => ω s.val)
      (fun ω : Environment => fun t : {z : Lattice // z ∈ T} => ω t.val)
      (environmentLaw μ) := by
  exact iIndepFun.indepFun_finset S T hST (iIndepFun_environment_eval μ)
    measurable_environment_eval

/-- Measurable observables of disjoint finite coordinate vectors are independent. -/
theorem indepFun_environment_observables (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (S T : Finset Lattice) (hST : Disjoint S T)
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {f : ({z : Lattice // z ∈ S} → ℝ) → α}
    {g : ({z : Lattice // z ∈ T} → ℝ) → β}
    (hf : Measurable f) (hg : Measurable g) :
    IndepFun (fun ω : Environment => f (fun s => ω s.val))
      (fun ω : Environment => g (fun t => ω t.val)) (environmentLaw μ) := by
  exact (indepFun_environment_restrict μ S T hST).comp hf hg

/-- Events determined by disjoint finite coordinate vectors have product probability. -/
theorem environmentLaw_restrict_inter (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (S T : Finset Lattice) (hST : Disjoint S T)
    (A : Set ({z : Lattice // z ∈ S} → ℝ))
    (B : Set ({z : Lattice // z ∈ T} → ℝ))
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    environmentLaw μ
        ((fun ω : Environment => fun s : {z : Lattice // z ∈ S} => ω s.val) ⁻¹' A ∩
          (fun ω : Environment => fun t : {z : Lattice // z ∈ T} => ω t.val) ⁻¹' B) =
      environmentLaw μ
          ((fun ω : Environment => fun s : {z : Lattice // z ∈ S} => ω s.val) ⁻¹' A) *
        environmentLaw μ
          ((fun ω : Environment => fun t : {z : Lattice // z ∈ T} => ω t.val) ⁻¹' B) := by
  exact (indepFun_environment_restrict μ S T hST).measure_inter_preimage_eq_mul A B hA hB

end LPPDifferentiability
