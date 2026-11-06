/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Animals.Family
import Mathlib.Data.Finset.Max

/-! Exact-size extensions of finite lattice animals.

Martin (2002), Lemma 3.1(i), uses this elementary fact without a separate proof.
We add a right neighbor at a site with maximal first coordinate and iterate.
-/

@[expose] public section

namespace LPPDifferentiability

private theorem isConnectedAnimal_insert_of_adj {s : Finset Lattice}
    (hs : IsConnectedAnimal s) {x y : Lattice} (hx : x ∈ s)
    (hxy : nearestNeighborGraph.Adj x y) : IsConnectedAnimal (insert y s) := by
  classical
  let f : nearestNeighborGraph.induce (↑s : Set Lattice) →g
      nearestNeighborGraph.induce (↑(insert y s) : Set Lattice) :=
    ⟨fun z => ⟨z.val, Finset.mem_insert_of_mem z.property⟩, fun h => h⟩
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).2
  refine ⟨⟨x, Finset.mem_insert_of_mem hx⟩, ?_⟩
  rintro ⟨z, hz⟩
  rcases Finset.mem_insert.mp hz with rfl | hz
  · exact SimpleGraph.Adj.reachable hxy
  · exact (hs.preconnected (⟨x, hx⟩ : s) ⟨z, hz⟩).map f

/-- A connected animal has a neighboring site outside it; adjoining it increases
its cardinality by exactly one and keeps the induced graph connected. -/
theorem IsConnectedAnimal.exists_extension_card_add_one {s : Finset Lattice}
    (hs : IsConnectedAnimal s) :
    ∃ t : Finset Lattice, IsConnectedAnimal t ∧ s ⊆ t ∧ t.card = s.card + 1 := by
  classical
  obtain ⟨⟨a, ha⟩⟩ := hs.nonempty
  obtain ⟨x, hx, hmax⟩ := s.exists_max_image Prod.fst ⟨a, ha⟩
  let y : Lattice := (x.1 + 1, x.2)
  have hy : y ∉ s := by
    intro hymem
    have hle := hmax y hymem
    change x.1 + 1 ≤ x.1 at hle
    omega
  have hxy : nearestNeighborGraph.Adj x y := by
    left
    constructor
    · change |x.1 - (x.1 + 1)| = 1
      simp only [sub_add_cancel_left, abs_neg, abs_one]
    · rfl
  exact ⟨insert y s, isConnectedAnimal_insert_of_adj hs hx hxy,
    Finset.subset_insert y s, Finset.card_insert_of_notMem hy⟩

/-- Any connected animal can be enlarged to any larger exact size. -/
theorem IsConnectedAnimal.exists_extension_card {s : Finset Lattice}
    (hs : IsConnectedAnimal s) (N : ℕ) (hN : s.card ≤ N) :
    ∃ t : Finset Lattice, IsConnectedAnimal t ∧ s ⊆ t ∧ t.card = N := by
  suffices h : ∀ k : ℕ, ∃ t : Finset Lattice,
      IsConnectedAnimal t ∧ s ⊆ t ∧ t.card = s.card + k by
    obtain ⟨t, ht, hst, hcard⟩ := h (N - s.card)
    exact ⟨t, ht, hst, by omega⟩
  intro k
  induction k with
  | zero => exact ⟨s, hs, Finset.Subset.refl s, by omega⟩
  | succ k ih =>
    obtain ⟨t, ht, hst, hcard⟩ := ih
    obtain ⟨u, hu, htu, hucard⟩ := ht.exists_extension_card_add_one
    exact ⟨u, hu, hst.trans htu, by omega⟩

/-- An animal containing zero extends to a member of the existing rooted family. -/
theorem IsConnectedAnimal.exists_extension_mem_animalFamily {s : Finset Lattice}
    (hs : IsConnectedAnimal s) (hzero : (0 : Lattice) ∈ s)
    (N : ℕ) (hN : s.card ≤ N) :
    ∃ t ∈ animalFamily N, s ⊆ t := by
  obtain ⟨t, ht, hst, hcard⟩ := hs.exists_extension_card N hN
  exact ⟨t, (mem_animalFamily_iff N t).2 ⟨ht, hst hzero, hcard⟩, hst⟩

end LPPDifferentiability
