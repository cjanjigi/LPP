/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Probability.PassageMeasurable
public import LPP_Foundations.Model.LastPassage.Basic
public import Mathlib.MeasureTheory.Measure.Real

/-! Finite intersections of passage events, and families of maximizing paths. -/

public section

open MeasureTheory Set
open scoped BigOperators

namespace LPPDifferentiability

/-- The finite union bound, without an independence assumption. -/
theorem finite_intersection_probability_lower_bound
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (B : ℕ) (E : Fin B → Set Ω) (q : ℝ)
    (hm : ∀ j, MeasurableSet (E j)) (hq : ∀ j, q ≤ ν.real (E j)) :
    max 0 (1 - (B : ℝ) * (1 - q)) ≤ ν.real (⋂ j, E j) := by
  have hmAll : MeasurableSet (⋂ j, E j) := MeasurableSet.iInter hm
  have hcomp : ν.real (⋂ j, E j)ᶜ ≤ (B : ℝ) * (1 - q) := by
    rw [compl_iInter]
    calc
      ν.real (⋃ j, (E j)ᶜ) ≤ ∑ j, ν.real (E j)ᶜ :=
        measureReal_iUnion_fintype_le _
      _ ≤ ∑ _j : Fin B, (1 - q) := by
        apply Finset.sum_le_sum
        intro j _hj
        rw [probReal_compl_eq_one_sub (hm j)]
        linarith only [hq j]
      _ = (B : ℝ) * (1 - q) := by simp; ring
  rw [probReal_compl_eq_one_sub hmAll] at hcomp
  exact max_le measureReal_nonneg (by linarith only [hcomp])

/-- A family exists exactly when the maxima of the pieces satisfy the bounds.
This also covers an empty family and zero-length pieces. -/
theorem exists_maximizing_family_iff (B : ℕ) (u : Fin B → Lattice)
    (d : Fin B → ℕ × ℕ) (a : Fin B → ℝ) (ω : Environment) :
    (∃ p : (j : Fin B) → Path (u j) (d j), ∀ j,
      pathWeight ω (p j) = lastPassage ω (u j) (d j) ∧
      a j ≤ pathWeight ω (p j)) ↔
    ∀ j, a j ≤ lastPassage ω (u j) (d j) := by
  constructor
  · rintro ⟨p, hp⟩ j
    rw [← (hp j).1]
    exact (hp j).2
  · intro h
    have hex (j : Fin B) : ∃ p : Path (u j) (d j),
        pathWeight ω p = lastPassage ω (u j) (d j) ∧ a j ≤ pathWeight ω p := by
      obtain ⟨p, hp⟩ := exists_pathWeight_eq_lastPassage ω (u j) (d j)
      exact ⟨p, hp, hp.symm ▸ h j⟩
    exact Classical.axiomOfChoice hex

/-- The family event is measurable, since it is given by finitely many LPP
inequalities. -/
theorem measurableSet_exists_maximizing_family (B : ℕ) (u : Fin B → Lattice)
    (d : Fin B → ℕ × ℕ) (a : Fin B → ℝ) :
    MeasurableSet {ω : Environment |
      ∃ p : (j : Fin B) → Path (u j) (d j), ∀ j,
        pathWeight ω (p j) = lastPassage ω (u j) (d j) ∧
        a j ≤ pathWeight ω (p j)} := by
  simp only [exists_maximizing_family_iff, ofPred_forall]
  exact MeasurableSet.iInter fun j =>
    measurableSet_le measurable_const (measurable_lastPassage (u j) (d j))

end LPPDifferentiability
