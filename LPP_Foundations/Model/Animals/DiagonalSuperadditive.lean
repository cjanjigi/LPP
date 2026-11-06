/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Animals.DiagonalGluing
public import LPP_Foundations.Model.Animals.DiagonalMaximum

/-! Superadditivity of Martin's diagonal animal maximum. -/

@[expose] public section

namespace LPPDifferentiability

/-- The diagonal animal maximum is superadditive on successive integer
intervals, for arbitrary signed site fields. -/
theorem diagonalAnimalMaximum_superadditive {l m n : ℤ}
    (hlm : l < m) (hmn : m < n) (w : Lattice → ℝ) :
    diagonalAnimalMaximum l m hlm w + diagonalAnimalMaximum m n hmn w ≤
      diagonalAnimalMaximum l n (lt_trans hlm hmn) w := by
  obtain ⟨s, hs, hsm⟩ :=
    exists_diagonalAnimalWeight_eq_diagonalAnimalMaximum l m hlm w
  obtain ⟨t, ht, htn⟩ :=
    exists_diagonalAnimalWeight_eq_diagonalAnimalMaximum m n hmn w
  have hst : s ∪ t ∈ diagonalAnimalFamily l n :=
    diagonalAnimalFamily_union hlm hmn hs ht
  calc
    diagonalAnimalMaximum l m hlm w + diagonalAnimalMaximum m n hmn w =
        animalWeight w s + animalWeight w t := by rw [← hsm, ← htn]
    _ = animalWeight w (s ∪ t) :=
      (animalWeight_union_of_mem_diagonalAnimalFamily w hs ht).symm
    _ ≤ diagonalAnimalMaximum l n (lt_trans hlm hmn) w :=
      diagonalAnimalWeight_le_diagonalAnimalMaximum l n (lt_trans hlm hmn) w hst

end LPPDifferentiability
