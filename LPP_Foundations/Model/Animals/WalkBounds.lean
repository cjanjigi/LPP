/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Animals.Traversal
public import LPP_Foundations.Model.Animals.BoxCardinality
import Lean.Elab.Tactic.Omega

/-! Simple paths give the exact radius `card - 1` bound for lattice animals. -/

@[expose] public section

namespace LPPDifferentiability

/-- The displacement in either coordinate is bounded by the number of walk edges. -/
theorem nearestNeighborGraph_walk_coordinate_bounds {x y : Lattice}
    (p : nearestNeighborGraph.Walk x y) :
    |y.1 - x.1| ≤ (p.length : ℤ) ∧ |y.2 - x.2| ≤ (p.length : ℤ) := by
  induction p with
  | nil => simp only [sub_self, abs_zero, SimpleGraph.Walk.length_nil, Nat.cast_zero,
      le_refl, and_self]
  | @cons x z y hxz p ih =>
    obtain ⟨h₁, h₂⟩ := nearestNeighborGraph_adj_coordinate_bounds hxz
    simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
    constructor
    · calc
        |y.1 - x.1| ≤ |y.1 - z.1| + |z.1 - x.1| := abs_sub_le _ _ _
        _ ≤ (p.length : ℤ) + 1 := add_le_add ih.1 h₁
    · calc
        |y.2 - x.2| ≤ |y.2 - z.2| + |z.2 - x.2| := abs_sub_le _ _ _
        _ ≤ (p.length : ℤ) + 1 := add_le_add ih.2 h₂

/-- Connectivity gives a walk to each site with at most `card - 1` edges.
The walk comes from a simple path in the finite induced graph. -/
theorem exists_animal_walk_length_le (s : Finset Lattice) (hs : IsConnectedAnimal s)
    {x y : Lattice} (hx : x ∈ s) (hy : y ∈ s) :
    ∃ p : nearestNeighborGraph.Walk x y,
      p.length ≤ s.card - 1 ∧ ∀ z ∈ p.support, z ∈ s := by
  classical
  obtain ⟨p, hp⟩ := hs.exists_isPath (⟨x, hx⟩ : s) (⟨y, hy⟩ : s)
  have hlen := hp.length_lt
  change p.length < Fintype.card s at hlen
  rw [Fintype.card_coe] at hlen
  let f : nearestNeighborGraph.induce (↑s : Set Lattice) →g nearestNeighborGraph :=
    ⟨Subtype.val, fun h => h⟩
  refine ⟨p.map f, ?_, ?_⟩
  · rw [SimpleGraph.Walk.length_map]
    omega
  · intro z hz
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
    obtain ⟨v, _, rfl⟩ := hz
    exact v.property

/-- Any animal containing zero lies in the box of strict radius `card`, which is
the closed integer box of radius `card - 1`. -/
theorem animal_subset_integerBox (s : Finset Lattice) (hs : IsConnectedAnimal s)
    (hzero : (0 : Lattice) ∈ s) : s ⊆ integerBox 0 (s.card - 1) := by
  intro z hz
  obtain ⟨p, hlen, _⟩ := exists_animal_walk_length_le s hs hzero hz
  obtain ⟨h₁, h₂⟩ := nearestNeighborGraph_walk_coordinate_bounds p
  apply (mem_integerBox_iff 0 z (s.card - 1)).2
  have hcast : (p.length : ℤ) ≤ ((s.card - 1 : ℕ) : ℤ) := by exact_mod_cast hlen
  exact ⟨h₁.trans hcast, h₂.trans hcast⟩

end LPPDifferentiability
