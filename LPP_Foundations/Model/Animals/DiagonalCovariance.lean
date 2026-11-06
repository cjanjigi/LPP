/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Animals.DiagonalMaximum
public import LPP_Foundations.Model.Animals.DiagonalTranslation

/-! Translation covariance of the signed diagonal-animal maximum. -/

public section

namespace LPPDifferentiability

/-- Translating the field shifts both endpoints of the maximum.
The two bounds use maximizing animals and their translated finite sets. -/
theorem diagonalAnimalMaximum_translate (m n k : ℤ) (hmn : m < n)
    (w : Lattice → ℝ) :
    diagonalAnimalMaximum m n hmn (fun z => w ((k, k) + z)) =
      diagonalAnimalMaximum (m + k) (n + k) (by omega) w := by
  apply le_antisymm
  · obtain ⟨s, hs, hmax⟩ :=
      exists_diagonalAnimalWeight_eq_diagonalAnimalMaximum m n hmn
        (fun z => w ((k, k) + z))
    rw [← hmax, ← animalWeight_image_lattice_add]
    exact diagonalAnimalWeight_le_diagonalAnimalMaximum (m + k) (n + k)
      (by omega) w (image_mem_diagonalAnimalFamily hs k)
  · obtain ⟨s, hs, hmax⟩ :=
      exists_diagonalAnimalWeight_eq_diagonalAnimalMaximum (m + k) (n + k)
        (by omega) w
    have hinv : s.image (fun z => (-k, -k) + z) ∈ diagonalAnimalFamily m n := by
      simpa only [add_neg_cancel_right] using image_mem_diagonalAnimalFamily hs (-k)
    have hweight :
        animalWeight (fun z => w ((k, k) + z))
          (s.image (fun z => (-k, -k) + z)) = animalWeight w s := by
      rw [animalWeight_image_lattice_add]
      have hcancel : (fun z : Lattice => w ((k, k) + ((-k, -k) + z))) = w := by
        funext z
        apply congrArg w
        apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, add_neg_cancel_left]
      rw [hcancel]
    calc
      _ = animalWeight w s := hmax.symm
      _ = animalWeight (fun z => w ((k, k) + z))
          (s.image (fun z => (-k, -k) + z)) := hweight.symm
      _ ≤ _ := diagonalAnimalWeight_le_diagonalAnimalMaximum m n hmn
        (fun z => w ((k, k) + z)) hinv

end LPPDifferentiability
