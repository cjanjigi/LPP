/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.Animals.ExcessClassSum
public import LPP_Foundations.Frozen.Model.Environment
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! One animal, chosen from the geometry alone, bounds every environment's finite excess sum. -/

public section
namespace LPPDifferentiability
open scoped BigOperators

/-- The animal is chosen from the geometry before all environments. The support
is an arbitrary finite set; producing the box is a later step. -/
theorem exists_excess_sum_animal_cover (A : Finset Lattice) (N : ℕ)
    (hzero : (0 : Lattice) ∈ A) (hcard : A.card ≤ N + 1)
    (hA : ((SimpleGraph.fromRel (fun x y : Lattice =>
      |x.1 - y.1| ≤ 2 ∧ |x.2 - y.2| ≤ 2)).induce (↑A : Set Lattice)).Connected)
    (α : Fin 4) (β : Fin 10) :
    ∃ B : Finset Lattice,
      A.image (fun b => ((b.1 - (α.val : ℤ)) / 4,
        (b.2 - (β.val : ℤ)) / 10)) ⊆ B ∧
      ((0 - (α.val : ℤ)) / 4, (0 - (β.val : ℤ)) / 10) ∈ B ∧
      IsConnectedAnimal B ∧ B.card ≤ 2 * (N + 1) ∧
      B.card + 1 ≤ 2 * A.card ∧
      ∀ (ω : Environment) (Q : Finset Lattice) (a s M : ℝ) (m : ℕ),
        let v : Lattice → Lattice := fun b =>
          let j : ℤ := ⌊(b.2 : ℝ) * s + a * ((b.1 * m : ℤ) : ℝ)⌋
          (j, b.1 * m - j)
        let Z : Lattice → ℝ := fun b =>
          ∑ z ∈ Q.map ⟨fun w => v b + w, fun _ _ h => add_left_cancel h⟩,
            max (ω z - M) 0
        (∑ b ∈ A.filter (fun b => b.1 % 4 = (α.val : ℤ) ∧
          b.2 % 10 = (β.val : ℤ)), Z b) ≤
        ∑ u ∈ B, Z (4 * u.1 + (α.val : ℤ), 10 * u.2 + (β.val : ℤ)) := by
  classical
  obtain ⟨B, hsub, hpoint, hconn, hsize⟩ :=
    exists_excess_coarsening_animal_cover A 0 hzero (α.val : ℤ) (β.val : ℤ) hA
  refine ⟨B, hsub, hpoint, hconn, by omega, hsize, ?_⟩
  intro ω Q a s M m
  dsimp only
  apply excess_class_sum_le_cover A B α β hsub
  intro b
  exact Finset.sum_nonneg (fun z _ => le_max_right (ω z - M) 0)

end LPPDifferentiability
