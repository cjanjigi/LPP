/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.LatticeNearNeighbours
public import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Count ordered close pairs in a finite signed lattice set by first-coordinate fibers. -/

public section

namespace LPPDifferentiability

/-- A finite signed lattice set has at most twelve ordered distinct close pairs per site. -/
theorem lattice_close_pairs_card_le_twelve_mul (Q : Finset Lattice) :
    ((Q ×ˢ Q).filter (fun pair => pair.1 ≠ pair.2 ∧
      |(pair.2.1 : ℝ) - (pair.1.1 : ℝ)| +
        |(pair.2.2 : ℝ) - (pair.1.2 : ℝ)| ≤ 2)).card ≤ 12 * Q.card := by
  classical
  let closePairs : Finset (Lattice × Lattice) :=
    (Q ×ˢ Q).filter (fun pair => pair.1 ≠ pair.2 ∧
      |(pair.2.1 : ℝ) - (pair.1.1 : ℝ)| +
        |(pair.2.2 : ℝ) - (pair.1.2 : ℝ)| ≤ 2)
  let fibers : Lattice → Finset (Lattice × Lattice) := fun u =>
    (Q.filter (fun v => u ≠ v ∧
      |(v.1 : ℝ) - (u.1 : ℝ)| + |(v.2 : ℝ) - (u.2 : ℝ)| ≤ 2)).image
      (fun v => (u, v))
  have partition : Q.biUnion fibers = closePairs := by
    ext pair
    rcases pair with ⟨u, v⟩
    constructor
    · intro hp
      rcases Finset.mem_biUnion.mp hp with ⟨a, ha, hp⟩
      rcases Finset.mem_image.mp hp with ⟨b, hb, hEq⟩
      rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩
      rcases Finset.mem_filter.mp hb with ⟨hbQ, hclose⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨ha, hbQ⟩, ?_⟩
      exact hclose
    · intro hp
      change (u, v) ∈ (Q ×ˢ Q).filter (fun pair => pair.1 ≠ pair.2 ∧
        |(pair.2.1 : ℝ) - (pair.1.1 : ℝ)| +
          |(pair.2.2 : ℝ) - (pair.1.2 : ℝ)| ≤ 2) at hp
      rcases Finset.mem_filter.mp hp with ⟨hp, hclose⟩
      rcases Finset.mem_product.mp hp with ⟨hu, hv⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨u, hu, ?_⟩
      apply Finset.mem_image.mpr
      refine ⟨v, Finset.mem_filter.mpr ⟨hv, hclose⟩, rfl⟩
  have fibers_pairwise_disjoint : (Q : Set Lattice).PairwiseDisjoint fibers := by
    intro u _ v _ huv
    change Disjoint (fibers u) (fibers v)
    rw [Finset.disjoint_left]
    intro pair hpu hpv
    rcases Finset.mem_image.mp hpu with ⟨a, _, hpu⟩
    rcases Finset.mem_image.mp hpv with ⟨b, _, hpv⟩
    have hEq : (u, a) = (v, b) := hpu.trans hpv.symm
    exact huv (congrArg Prod.fst hEq)
  have fiber_card (u : Lattice) : (fibers u).card ≤ 12 := by
    obtain ⟨N, hN, hNcard⟩ := exists_lattice_l1_neighbors_card_eq_twelve u
    have hsubset :
        Q.filter (fun v => u ≠ v ∧
          |(v.1 : ℝ) - (u.1 : ℝ)| + |(v.2 : ℝ) - (u.2 : ℝ)| ≤ 2) ⊆ N := by
      intro v hv
      rcases Finset.mem_filter.mp hv with ⟨_, hclose⟩
      apply (hN v).2
      exact ⟨Ne.symm hclose.1, hclose.2⟩
    have hmap_injective : Function.Injective (fun v : Lattice => (u, v)) := by
      intro v w hEq
      exact congrArg Prod.snd hEq
    dsimp [fibers]
    rw [Finset.card_image_of_injective _ hmap_injective]
    exact (Finset.card_le_card hsubset).trans_eq hNcard
  change closePairs.card ≤ 12 * Q.card
  calc
    closePairs.card = (Q.biUnion fibers).card := by rw [← partition]
    _ = ∑ u ∈ Q, (fibers u).card := Finset.card_biUnion fibers_pairwise_disjoint
    _ ≤ ∑ u ∈ Q, 12 := by
      apply Finset.sum_le_sum
      intro u _
      exact fiber_card u
    _ = 12 * Q.card := by simp [Nat.mul_comm]

end LPPDifferentiability

end
