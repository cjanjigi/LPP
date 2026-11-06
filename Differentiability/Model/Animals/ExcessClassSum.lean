/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.ExcessBlockResidues
public import Differentiability.Model.Animals.ExcessCoarsening
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Exact finite reindexing of signed residue classes, and nonnegative enlargement. -/

public section
namespace LPPDifferentiability
open scoped BigOperators

/-- On a residue class, the signed coarsening has an explicit affine inverse. -/
theorem excess_class_coarsening_inverse (α : Fin 4) (β : Fin 10) (b : Lattice)
    (hb : b.1 % 4 = (α.val : ℤ) ∧ b.2 % 10 = (β.val : ℤ)) :
    (4 * ((b.1 - (α.val : ℤ)) / 4) + (α.val : ℤ),
      10 * ((b.2 - (β.val : ℤ)) / 10) + (β.val : ℤ)) = b := by
  obtain ⟨v, rfl⟩ := (excess_residue_index_iff α β b).mp hb
  apply Prod.ext <;> dsimp only <;> omega

/-- Reindex the filtered class; injectivity follows from the inverse. -/
theorem excess_class_sum_reindex (A : Finset Lattice) (α : Fin 4) (β : Fin 10)
    (Z : Lattice → ℝ) :
    (∑ b ∈ A.filter (fun b => b.1 % 4 = (α.val : ℤ) ∧
      b.2 % 10 = (β.val : ℤ)), Z b) =
    ∑ v ∈ (A.filter (fun b => b.1 % 4 = (α.val : ℤ) ∧
      b.2 % 10 = (β.val : ℤ))).image
        (fun b => ((b.1 - (α.val : ℤ)) / 4, (b.2 - (β.val : ℤ)) / 10)),
      Z (4 * v.1 + (α.val : ℤ), 10 * v.2 + (β.val : ℤ)) := by
  classical
  let C := A.filter (fun b => b.1 % 4 = (α.val : ℤ) ∧ b.2 % 10 = (β.val : ℤ))
  let ψ : Lattice → Lattice := fun b =>
    ((b.1 - (α.val : ℤ)) / 4, (b.2 - (β.val : ℤ)) / 10)
  let φ : Lattice → Lattice := fun v =>
    (4 * v.1 + (α.val : ℤ), 10 * v.2 + (β.val : ℤ))
  have hinv : ∀ b ∈ C, φ (ψ b) = b := by
    intro b hb
    exact excess_class_coarsening_inverse α β b (Finset.mem_filter.mp hb).2
  have hinj : Set.InjOn ψ (↑C : Set Lattice) := by
    intro b hb c hc he
    calc b = φ (ψ b) := (hinv b hb).symm
         _ = φ (ψ c) := congrArg φ he
         _ = c := hinv c hc
  change (∑ b ∈ C, Z b) = ∑ v ∈ C.image ψ, Z (φ v)
  rw [Finset.sum_image hinj]
  exact Finset.sum_congr rfl (fun b hb => congrArg Z (hinv b hb).symm)

/-- Enlarge through the full coarsening image to any containing finite set.
The weights are nonnegative data; no sum comparison is assumed. -/
theorem excess_class_sum_le_cover (A B : Finset Lattice) (α : Fin 4) (β : Fin 10)
    (hB : A.image (fun b =>
      ((b.1 - (α.val : ℤ)) / 4, (b.2 - (β.val : ℤ)) / 10)) ⊆ B)
    (Z : Lattice → ℝ) (hZ : ∀ b, 0 ≤ Z b) :
    (∑ b ∈ A.filter (fun b => b.1 % 4 = (α.val : ℤ) ∧
      b.2 % 10 = (β.val : ℤ)), Z b) ≤
    ∑ v ∈ B, Z (4 * v.1 + (α.val : ℤ), 10 * v.2 + (β.val : ℤ)) := by
  classical
  rw [excess_class_sum_reindex A α β Z]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro v hv
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hv
    exact hB (Finset.mem_image.mpr ⟨b, (Finset.mem_filter.mp hb).1, rfl⟩)
  · intro v _ _
    exact hZ _

end LPPDifferentiability
