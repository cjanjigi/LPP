/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Animals.DiagonalFamily
public import LPP_Foundations.Model.Animals.Maximum
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Lattice.Fold

/-! The signed maximum weight in Martin's planar diagonal animal family. -/

@[expose] public section

open scoped BigOperators

namespace LPPDifferentiability

/-- The maximum weight over exactly Martin's diagonal family for `m < n`.
There is no value for equal or backward intervals, where the family
need not be nonempty. -/
noncomputable def diagonalAnimalMaximum (m n : ℤ) (hmn : m < n)
    (w : Lattice → ℝ) : ℝ :=
  (diagonalAnimalFamily_finite m n).toFinset.sup'
    ((diagonalAnimalFamily_finite m n).toFinset_nonempty.mpr
      (diagonalAnimalFamily_nonempty m n hmn))
    (fun s => animalWeight w s)

/-- The proof that the interval is forward does not affect the maximum value. -/
theorem diagonalAnimalMaximum_proof_irrel (m n : ℤ)
    (hmn₁ hmn₂ : m < n) (w : Lattice → ℝ) :
    diagonalAnimalMaximum m n hmn₁ w = diagonalAnimalMaximum m n hmn₂ w := by
  cases Subsingleton.elim hmn₁ hmn₂
  rfl

/-- Every member of the diagonal family has weight at most the maximum. -/
theorem diagonalAnimalWeight_le_diagonalAnimalMaximum (m n : ℤ)
    (hmn : m < n) (w : Lattice → ℝ) {s : Finset Lattice}
    (hs : s ∈ diagonalAnimalFamily m n) :
    animalWeight w s ≤ diagonalAnimalMaximum m n hmn w := by
  classical
  have hs' : s ∈ (diagonalAnimalFamily_finite m n).toFinset :=
    (diagonalAnimalFamily_finite m n).mem_toFinset.mpr hs
  exact Finset.le_sup' (f := fun t => animalWeight w t) hs'

/-- Some member of the diagonal family attains the finite maximum. -/
theorem exists_diagonalAnimalWeight_eq_diagonalAnimalMaximum (m n : ℤ)
    (hmn : m < n) (w : Lattice → ℝ) :
    ∃ s ∈ diagonalAnimalFamily m n,
      animalWeight w s = diagonalAnimalMaximum m n hmn w := by
  classical
  let F := (diagonalAnimalFamily_finite m n).toFinset
  have hF : F.Nonempty :=
    (diagonalAnimalFamily_finite m n).toFinset_nonempty.mpr
      (diagonalAnimalFamily_nonempty m n hmn)
  obtain ⟨s, hs, hsup⟩ :=
    Finset.exists_mem_eq_sup' hF (fun t => animalWeight w t)
  refine ⟨s, (diagonalAnimalFamily_finite m n).mem_toFinset.mp ?_, ?_⟩
  · change s ∈ F
    exact hs
  · change animalWeight w s = F.sup' hF (fun t => animalWeight w t)
    exact hsup.symm

/-- The maximum is bounded above exactly when every member is. -/
theorem diagonalAnimalMaximum_le_iff (m n : ℤ) (hmn : m < n)
    (w : Lattice → ℝ) (u : ℝ) :
    diagonalAnimalMaximum m n hmn w ≤ u ↔
      ∀ s ∈ diagonalAnimalFamily m n, animalWeight w s ≤ u := by
  classical
  let F := (diagonalAnimalFamily_finite m n).toFinset
  have hF : F.Nonempty :=
    (diagonalAnimalFamily_finite m n).toFinset_nonempty.mpr
      (diagonalAnimalFamily_nonempty m n hmn)
  change F.sup' hF (fun s => animalWeight w s) ≤ u ↔
    ∀ s ∈ diagonalAnimalFamily m n, animalWeight w s ≤ u
  rw [Finset.sup'_le_iff]
  constructor
  · intro h s hs
    exact h s ((diagonalAnimalFamily_finite m n).mem_toFinset.mpr hs)
  · intro h s hs
    exact h s ((diagonalAnimalFamily_finite m n).mem_toFinset.mp hs)

/-- A threshold is below the maximum exactly when some member reaches it. -/
theorem le_diagonalAnimalMaximum_iff_exists_diagonalAnimalWeight_ge
    (m n : ℤ) (hmn : m < n) (w : Lattice → ℝ) (t : ℝ) :
    t ≤ diagonalAnimalMaximum m n hmn w ↔
      ∃ s ∈ diagonalAnimalFamily m n, t ≤ animalWeight w s := by
  classical
  let F := (diagonalAnimalFamily_finite m n).toFinset
  have hF : F.Nonempty :=
    (diagonalAnimalFamily_finite m n).toFinset_nonempty.mpr
      (diagonalAnimalFamily_nonempty m n hmn)
  change t ≤ F.sup' hF (fun s => animalWeight w s) ↔
    ∃ s ∈ diagonalAnimalFamily m n, t ≤ animalWeight w s
  rw [Finset.le_sup'_iff]
  constructor
  · rintro ⟨s, hs, ht⟩
    exact ⟨s, (diagonalAnimalFamily_finite m n).mem_toFinset.mp hs, ht⟩
  · rintro ⟨s, hs, ht⟩
    exact ⟨s, (diagonalAnimalFamily_finite m n).mem_toFinset.mpr hs, ht⟩

/-- Equality with `x` means that `x` bounds every member and is attained. -/
theorem diagonalAnimalMaximum_eq_iff (m n : ℤ) (hmn : m < n)
    (w : Lattice → ℝ) (x : ℝ) :
    diagonalAnimalMaximum m n hmn w = x ↔
      (∀ s ∈ diagonalAnimalFamily m n, animalWeight w s ≤ x) ∧
        ∃ s ∈ diagonalAnimalFamily m n, animalWeight w s = x := by
  constructor
  · intro hx
    constructor
    · intro s hs
      simpa [hx] using diagonalAnimalWeight_le_diagonalAnimalMaximum m n hmn w hs
    · obtain ⟨s, hs, hmax⟩ :=
        exists_diagonalAnimalWeight_eq_diagonalAnimalMaximum m n hmn w
      exact ⟨s, hs, by simpa [hx] using hmax⟩
  · rintro ⟨hupper, ⟨s, hs, hvalue⟩⟩
    apply le_antisymm
    · exact (diagonalAnimalMaximum_le_iff m n hmn w x).2 hupper
    · rw [← hvalue]
      exact diagonalAnimalWeight_le_diagonalAnimalMaximum m n hmn w hs

/-- Pointwise nonnegative site weights give a nonnegative diagonal maximum. -/
theorem diagonalAnimalMaximum_nonneg_of_forall_nonneg (m n : ℤ)
    (hmn : m < n) (w : Lattice → ℝ) (hw : ∀ v, 0 ≤ w v) :
    0 ≤ diagonalAnimalMaximum m n hmn w := by
  obtain ⟨s, hs, hmax⟩ :=
    exists_diagonalAnimalWeight_eq_diagonalAnimalMaximum m n hmn w
  rw [← hmax]
  exact Finset.sum_nonneg (fun v hv => hw v)

end LPPDifferentiability
