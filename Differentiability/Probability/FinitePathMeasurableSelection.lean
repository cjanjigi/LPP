/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Paths.Fintype
public import LPP_Foundations.Probability.PassageMeasurable
import Mathlib.Data.Fintype.EquivFin

/-!
# Measurable selection of a finite path

The event that a path stays in a region and exceeds a weight threshold is
measurable. On that event, choose a path measurably in the finite path space.
-/

@[expose] public section

namespace LPPDifferentiability

/-- The event that some actual `n`-step path from `u` stays in `R` and has
terminal-excluded weight strictly greater than `b` is measurable. -/
theorem measurableSet_exists_path_in_region_weight_gt
    (u : Lattice) (n : ℕ) (R : Finset Lattice) (b : ℝ) :
    MeasurableSet
      {ω : Environment |
        ∃ q : Σ i : Fin (n + 1), Path u (i.val, n - i.val),
          (∀ j : Fin (q.1.val + (n - q.1.val) + 1), q.2.vertex j ∈ R) ∧
            pathWeight ω q.2 > b} := by
  classical
  let Q := Σ i : Fin (n + 1), Path u (i.val, n - i.val)
  let verticesInR (q : Q) : Prop :=
    ∀ j : Fin (q.1.val + (n - q.1.val) + 1), q.2.vertex j ∈ R
  change MeasurableSet
    {ω : Environment | ∃ q : Q, verticesInR q ∧ pathWeight ω q.2 > b}
  have hEvent :
      {ω : Environment | ∃ q : Q, verticesInR q ∧ pathWeight ω q.2 > b} =
        ⋃ q : Q, {ω : Environment | verticesInR q ∧ pathWeight ω q.2 > b} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [hEvent]
  exact MeasurableSet.iUnion fun q => by
    by_cases hq : verticesInR q
    · simpa only [hq, true_and] using
        (measurableSet_lt measurable_const (measurable_pathWeight q.2))
    · simp [hq]

/-- On that event, a measurable selector chooses an actual path with every
vertex, including the terminal vertex, in `R` and actual path weight greater
than `b`. Measurability is stated for every subset of the finite target, which
is the discrete measurable structure on that target. -/
theorem exists_measurable_path_in_region_weight_gt_selector
    (u : Lattice) (n : ℕ) (R : Finset Lattice) (b : ℝ) :
    ∃ σ :
      {ω : Environment //
        ∃ q : Σ i : Fin (n + 1), Path u (i.val, n - i.val),
          (∀ j : Fin (q.1.val + (n - q.1.val) + 1), q.2.vertex j ∈ R) ∧
            pathWeight ω q.2 > b} →
        Σ i : Fin (n + 1), Path u (i.val, n - i.val),
      (∀ S : Set (Σ i : Fin (n + 1), Path u (i.val, n - i.val)),
        MeasurableSet {ω |
          σ ω ∈ S}) ∧
      (∀ ω : {ω : Environment //
        ∃ q : Σ i : Fin (n + 1), Path u (i.val, n - i.val),
          (∀ j : Fin (q.1.val + (n - q.1.val) + 1), q.2.vertex j ∈ R) ∧
            pathWeight ω q.2 > b},
        (∀ j : Fin ((σ ω).1.val + (n - (σ ω).1.val) + 1),
          (σ ω).2.vertex j ∈ R) ∧
          pathWeight ω.1 (σ ω).2 > b) := by
  classical
  let Q := Σ i : Fin (n + 1), Path u (i.val, n - i.val)
  let verticesInR (q : Q) : Prop :=
    ∀ j : Fin (q.1.val + (n - q.1.val) + 1), q.2.vertex j ∈ R
  let eligible (ω : Environment) (q : Q) : Prop :=
    verticesInR q ∧ pathWeight ω q.2 > b
  let E : Set Environment := {ω | ∃ q : Q, eligible ω q}
  change ∃ σ : {ω : Environment // ω ∈ E} → Q,
    (∀ S : Set Q, MeasurableSet {ω | σ ω ∈ S}) ∧
    (∀ ω : {ω : Environment // ω ∈ E}, eligible ω.1 (σ ω))
  let code : Q → ℕ := fun q => (Fintype.equivFin Q q).val
  have hcode : Function.Injective code :=
    Fin.val_injective.comp (Fintype.equivFin Q).injective
  have hleast (ω : {ω : Environment // ω ∈ E}) :
      ∃ q : Q, eligible ω.1 q ∧
        ∀ r : Q, eligible ω.1 r → code q ≤ code r := by
    let candidates := Finset.univ.filter (fun q : Q => eligible ω.1 q)
    have hne : candidates.Nonempty := by
      rcases ω.property with ⟨q, hq⟩
      exact ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ q, hq⟩⟩
    obtain ⟨q, hq, hmin⟩ := Finset.exists_min_image candidates code hne
    refine ⟨q, (Finset.mem_filter.mp hq).2, ?_⟩
    intro r hr
    exact hmin r (Finset.mem_filter.mpr ⟨Finset.mem_univ r, hr⟩)
  choose σ hσ using hleast
  have hEligible (q : Q) :
      MeasurableSet {ω : Environment | eligible ω q} := by
    by_cases hq : verticesInR q
    · simpa only [eligible, hq, true_and] using
        (measurableSet_lt measurable_const (measurable_pathWeight q.2))
    · simp [eligible, hq]
  have hleastMeas (q : Q) :
      MeasurableSet
        {ω : Environment | ∀ r : Q, eligible ω r → code q ≤ code r} := by
    have hInter :
        {ω : Environment | ∀ r : Q, eligible ω r → code q ≤ code r} =
          ⋂ r : Q, {ω : Environment | eligible ω r → code q ≤ code r} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    rw [hInter]
    apply MeasurableSet.iInter
    intro r
    by_cases hqr : code q ≤ code r
    · simp [hqr]
    · have hComplement :
          {ω : Environment | eligible ω r → code q ≤ code r} =
            ({ω : Environment | eligible ω r} : Set Environment)ᶜ := by
        ext ω
        simp [hqr]
      rw [hComplement]
      exact (hEligible r).compl
  have hCoreMeas (q : Q) :
      MeasurableSet
        {ω : Environment | eligible ω q ∧
          ∀ r : Q, eligible ω r → code q ≤ code r} := by
    exact (hEligible q).inter (hleastMeas q)
  have hFiber (q : Q) :
      {ω : {ω : Environment // ω ∈ E} | σ ω = q} =
        {ω : {ω : Environment // ω ∈ E} |
          eligible ω.1 q ∧
            ∀ r : Q, eligible ω.1 r → code q ≤ code r} := by
    ext ω
    constructor
    · intro h
      have hσ' := hσ ω
      rw [h] at hσ'
      exact hσ'
    · rintro ⟨hq, hmin⟩
      apply hcode
      exact le_antisymm ((hσ ω).2 q hq) (hmin (σ ω) (hσ ω).1)
  have hFiberMeas (q : Q) :
      MeasurableSet {ω : {ω : Environment // ω ∈ E} | σ ω = q} := by
    rw [hFiber q]
    exact (hCoreMeas q).preimage measurable_subtype_coe
  refine ⟨σ, ?_, ?_⟩
  · intro S
    have hUnion :
        {ω : {ω : Environment // ω ∈ E} | σ ω ∈ S} =
          ⋃ q : Q,
            {ω : {ω : Environment // ω ∈ E} | σ ω = q ∧ q ∈ S} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · intro hω
        exact ⟨σ ω, rfl, hω⟩
      · rintro ⟨q, hq, hS⟩
        rw [hq]
        exact hS
    rw [hUnion]
    apply MeasurableSet.iUnion
    intro q
    by_cases hq : q ∈ S
    · simpa [hq] using hFiberMeas q
    · simp [hq]
  · intro ω
    exact (hσ ω).1

end LPPDifferentiability
