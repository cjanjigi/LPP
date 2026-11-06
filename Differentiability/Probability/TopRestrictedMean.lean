/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.RestrictedPathMaximum
public import LPP_Foundations.Probability.FiniteEnvironmentLaw
public import Differentiability.Probability.TopIndicatorLaw
public import LPP_Foundations.Model.LastPassage.Bounds
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# The finite top-count law and its passage comparison

The restricted maximum of the top-site count is a function of finitely many Boolean
variables. This file compares its law and its mean with those of the passage of
the whole environment.
-/

public section

open MeasureTheory Set

namespace LPPDifferentiability

open Classical in
/-- The finite Boolean vector has the product law. The restricted maximum is
measurable and integrable, its mean in the original space equals its mean under
the finite law, and its zero extension is dominated by the whole top-indicator
field. -/
theorem source_top_restricted_transport
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (R : Finset Lattice) (u : Lattice) (d : ℕ × ℕ) :
    let M : EReal := sSup ((fun t : ℝ => (t : EReal)) '' μ.support)
    let c : ℝ → Bool := fun t => if (t : EReal) = M then true else false
    let χ : ℝ → ℝ := fun t => if (t : EReal) = M then 1 else 0
    let I : Type := {z : Lattice // z ∈ R}
    let Eligible : Type :=
      {p : Path u d // ∀ j : Fin (d.1 + d.2 + 1), p.vertex j ∈ R}
    let P : Finset Eligible := Finset.univ
    let count : Eligible → (I → Bool) → ℕ := fun p x =>
      (p.val.collectedSites.filter
        (fun z => if hz : z ∈ R then x ⟨z, hz⟩ = true else False)).card
    let F : (I → Bool) → ℝ := fun x => (↑(P.sup (fun p => count p x) : ℕ) : ℝ)
    let X : Environment → I → Bool := fun ω i => c (ω i.val)
    let ν : Measure (I → Bool) := Measure.pi (fun _ : I => μ.map c)
    Measurable c ∧ Measurable X ∧ (environmentLaw μ).map X = ν ∧
      Measurable F ∧ Integrable F ν ∧
      Integrable (fun ω => F (X ω)) (environmentLaw μ) ∧
      (∫ ω, F (X ω) ∂environmentLaw μ) = (∫ x, F x ∂ν) ∧
      (∀ ω, F (X ω) ≤ lastPassage (fun z => χ (ω z)) u d) := by
  classical
  dsimp only
  let M : EReal := sSup ((fun t : ℝ => (t : EReal)) '' μ.support)
  let c : ℝ → Bool := fun t => if (t : EReal) = M then true else false
  let χ : ℝ → ℝ := fun t => if (t : EReal) = M then 1 else 0
  let I : Type := {z : Lattice // z ∈ R}
  let Eligible : Type :=
    {p : Path u d // ∀ j : Fin (d.1 + d.2 + 1), p.vertex j ∈ R}
  let P : Finset Eligible := Finset.univ
  let count : Eligible → (I → Bool) → ℕ := fun p x =>
    (p.val.collectedSites.filter
      (fun z => if hz : z ∈ R then x ⟨z, hz⟩ = true else False)).card
  let F : (I → Bool) → ℝ := fun x => (↑(P.sup (fun p => count p x) : ℕ) : ℝ)
  let X : Environment → I → Bool := fun ω i => c (ω i.val)
  let ν : Measure (I → Bool) := Measure.pi (fun _ : I => μ.map c)
  change Measurable c ∧ Measurable X ∧ (environmentLaw μ).map X = ν ∧
    Measurable F ∧ Integrable F ν ∧
    Integrable (fun ω => F (X ω)) (environmentLaw μ) ∧
    (∫ ω, F (X ω) ∂environmentLaw μ) = (∫ x, F x ∂ν) ∧
    (∀ ω, F (X ω) ≤ lastPassage (fun z => χ (ω z)) u d)
  have hc : Measurable c := Measurable.ite
    (source_top_indicator_event_measurable μ) measurable_const measurable_const
  have hX : Measurable X := measurable_pi_iff.mpr fun i =>
    hc.comp (measurable_environment_eval i.val)
  have hlaw : (environmentLaw μ).map X = ν :=
    environmentLaw_map_finite_coordinates_comp μ Subtype.val Subtype.val_injective c hc
  have hF : Measurable F := restrictedPathCountMaximum_measurable u d R
  have hnonneg : ∀ x, 0 ≤ F x := restrictedPathCountMaximum_nonneg u d R
  have hbound : ∀ x, |F x| ≤ (d.1 + d.2 : ℕ) := by
    intro x
    rw [abs_of_nonneg (hnonneg x)]
    exact restrictedPathCountMaximum_le_length u d R x
  have hi : Integrable F ν := Integrable.of_bound hF.aestronglyMeasurable
    ((d.1 + d.2 : ℕ) : ℝ) (Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using hbound x)
  have hi_map : Integrable F ((environmentLaw μ).map X) := hlaw.symm ▸ hi
  refine ⟨hc, hX, hlaw, hF, hi, hi_map.comp_measurable hX, ?_, ?_⟩
  · rw [← hlaw]
    exact (integral_map_of_stronglyMeasurable hX hF.stronglyMeasurable).symm
  · intro ω
    let extended : Environment := fun z =>
      if hz : z ∈ R then if X ω ⟨z, hz⟩ then (1 : ℝ) else 0 else 0
    have hdom : ∀ z, extended z ≤ χ (ω z) := by
      intro z
      by_cases hz : z ∈ R
      · by_cases ht : (ω z : EReal) = M <;> simp [extended, X, c, χ, hz, ht]
      · dsimp [extended]
        rw [dite_eq_right hz]
        exact (source_top_indicator_mem_unitInterval μ (ω z)).1
    exact (restrictedPathCountMaximum_le_lastPassage u d R (X ω)).trans
      (lastPassage_mono extended (fun z => χ (ω z)) u d hdom)

open Classical in
/-- The event that the maximum exceeds `b` is exactly the event that some confined
path collects more than `b` top sites. The threshold condition accounts for the
zero convention when no path exists. -/
theorem source_top_restricted_gt_iff
    (μ : Measure ℝ) (R : Finset Lattice) (u : Lattice) (d : ℕ × ℕ) :
    let M : EReal := sSup ((fun t : ℝ => (t : EReal)) '' μ.support)
    let I : Type := {z : Lattice // z ∈ R}
    let Eligible : Type :=
      {p : Path u d // ∀ j : Fin (d.1 + d.2 + 1), p.vertex j ∈ R}
    let P : Finset Eligible := Finset.univ
    let count : Eligible → (I → Bool) → ℕ := fun p x =>
      (p.val.collectedSites.filter
        (fun z => if hz : z ∈ R then x ⟨z, hz⟩ = true else False)).card
    let F : (I → Bool) → ℝ := fun x => (↑(P.sup (fun p => count p x) : ℕ) : ℝ)
    let X : Environment → I → Bool := fun ω i =>
      if (ω i.val : EReal) = M then true else false
    ∀ (ω : Environment) (b : ℝ), 0 ≤ b →
      (F (X ω) > b ↔ ∃ p : Path u d,
        (∀ j : Fin (d.1 + d.2 + 1), p.vertex j ∈ R) ∧
        b < ((p.collectedSites.filter (fun z => (ω z : EReal) = M)).card : ℝ)) := by
  classical
  intro M I Eligible P count F X ω b hb
  have hcount (p : Eligible) : count p (X ω) =
      (p.val.collectedSites.filter (fun z => (ω z : EReal) = M)).card := by
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro z hz
    obtain ⟨j, rfl⟩ := (p.val.mem_collectedSites_iff z).mp hz
    have hj := p.property j.castSucc
    simp [X, hj]
  rw [restrictedPathCountMaximum_gt_iff u d R (X ω) b hb]
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p.val, p.property, ?_⟩
    change b < (count p (X ω) : ℝ) at hp
    rw [hcount p] at hp
    exact hp
  · rintro ⟨p, hp, h⟩
    refine ⟨⟨p, hp⟩, ?_⟩
    change b < (count ⟨p, hp⟩ (X ω) : ℝ)
    rw [hcount ⟨p, hp⟩]
    exact h

end LPPDifferentiability
