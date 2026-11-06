/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.Lattice
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega

/-! Finite nearest-neighbor animals and closed walks visiting every site.

The doubled-tree traversal is built by adding one new vertex and a two-edge excursion
at a time. Martin (2002), Lemma 2.1, is stated there without proof. This construction is
new; it is not taken from the proof of Cox et al. (1993).
-/

@[expose] public section

namespace LPPDifferentiability

/-- The usual nearest-neighbor graph on the integer plane. -/
def nearestNeighborGraph : SimpleGraph Lattice where
  Adj x y := (|x.1 - y.1| = 1 ∧ x.2 = y.2) ∨
    (x.1 = y.1 ∧ |x.2 - y.2| = 1)
  symm := by
    constructor
    intro x y h
    simpa only [abs_sub_comm, eq_comm] using h
  loopless := by
    constructor
    intro x
    simp only [sub_self, abs_zero, zero_ne_one, false_and, and_false, or_self,
      not_false_eq_true]

/-- A finite set is an animal when its induced nearest-neighbor graph is connected.
The origin and the cardinality are kept as separate hypotheses. -/
def IsConnectedAnimal (s : Finset Lattice) : Prop :=
  (nearestNeighborGraph.induce (↑s : Set Lattice)).Connected

private theorem walk_end_mem_of_adj_closed {V : Type*} {G : SimpleGraph V}
    (S : Set V) (hclosed : ∀ x ∈ S, ∀ y, G.Adj x y → y ∈ S)
    {a b : V} (p : G.Walk a b) (ha : a ∈ S) : b ∈ S := by
  induction p with
  | nil => exact ha
  | @cons a c b hac p ih => exact ih (hclosed a ha c hac)

private theorem exists_edge_outside_walk {V : Type*} {G : SimpleGraph V}
    (hG : G.Connected) {a : V} (p : G.Walk a a)
    (y : V) (hy : y ∉ p.support) :
    ∃ x ∈ p.support, ∃ z, z ∉ p.support ∧ G.Adj x z := by
  classical
  by_contra hn
  push Not at hn
  have hc : ∀ x ∈ {v | v ∈ p.support}, ∀ z, G.Adj x z → z ∈ p.support := by
    intro x hx z hxz
    by_contra hz
    exact hn x hx z hz hxz
  obtain ⟨q⟩ := hG.preconnected a y
  exact hy (walk_end_mem_of_adj_closed {v | v ∈ p.support} hc q p.start_mem_support)

private theorem exists_closed_walk_cover_aux {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hG : G.Connected) {a : V} (m : ℕ) :
    ∀ p : G.Walk a a, Fintype.card V - p.support.toFinset.card = m →
      ∃ q : G.Walk a a, q.length ≤ p.length + 2 * m ∧ ∀ v, v ∈ q.support := by
  classical
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro p hm
    by_cases hall : ∀ v, v ∈ p.support
    · exact ⟨p, by omega, hall⟩
    push Not at hall
    obtain ⟨y, hy⟩ := hall
    obtain ⟨x, hx, z, hz, hxz⟩ := exists_edge_outside_walk hG p y hy
    obtain ⟨p₁, p₂, hp⟩ := SimpleGraph.Walk.mem_support_iff_exists_append.mp hx
    let q : G.Walk a a := p₁.append (.cons hxz (.cons hxz.symm p₂))
    have hsupport : q.support.toFinset = insert z p.support.toFinset := by
      ext v
      simp only [q, hp, SimpleGraph.Walk.mem_support_append_iff,
        SimpleGraph.Walk.support_cons, List.mem_toFinset, List.mem_cons,
        Finset.mem_insert]
      have hxv : v = x → v ∈ p₁.support := by
        intro hvx
        rw [hvx]
        exact p₁.end_mem_support
      tauto
    have hcard : q.support.toFinset.card = p.support.toFinset.card + 1 := by
      rw [hsupport, Finset.card_insert_of_notMem (by simpa only [List.mem_toFinset] using hz)]
    have hcard_lt : p.support.toFinset.card < Fintype.card V := by
      apply Finset.card_lt_card
      exact Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, by
        intro heq
        have : z ∈ p.support.toFinset := by rw [heq]; exact Finset.mem_univ z
        exact hz (List.mem_toFinset.mp this)⟩
    have hmissing : Fintype.card V - q.support.toFinset.card < m := by omega
    obtain ⟨r, hrlen, hrcover⟩ := ih _ hmissing q rfl
    have hqlen : q.length = p.length + 2 := by
      simp only [q, hp, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons]
      omega
    exact ⟨r, by omega, hrcover⟩

/-- A finite connected graph has a closed walk from any root visiting every
vertex, using at most twice the number of vertices minus two edges. -/
theorem exists_closed_walk_cover {V : Type*} [Fintype V]
    {G : SimpleGraph V} (hG : G.Connected) (a : V) :
    ∃ p : G.Walk a a, p.length ≤ 2 * (Fintype.card V - 1) ∧
      ∀ v, v ∈ p.support := by
  classical
  simpa only [SimpleGraph.Walk.support_nil, List.toFinset_cons, List.toFinset_nil,
    Finset.insert_empty, Finset.card_singleton, SimpleGraph.Walk.length_nil, zero_add]
    using exists_closed_walk_cover_aux hG (a := a) (Fintype.card V - 1) .nil
      (by simp only [SimpleGraph.Walk.support_nil, List.toFinset_cons,
        List.toFinset_nil, Finset.insert_empty, Finset.card_singleton])

/-- An animal containing zero has a closed nearest-neighbor walk
whose support is exactly the animal and whose length is at most `2(card-1)`. -/
theorem exists_animal_traversal (s : Finset Lattice) (hs : IsConnectedAnimal s)
    (hzero : (0 : Lattice) ∈ s) :
    ∃ p : nearestNeighborGraph.Walk 0 0,
      p.length ≤ 2 * (s.card - 1) ∧ ∀ z, z ∈ p.support ↔ z ∈ s := by
  classical
  obtain ⟨p, hlen, hcover⟩ := exists_closed_walk_cover hs (⟨0, hzero⟩ : s)
  let f : nearestNeighborGraph.induce (↑s : Set Lattice) →g nearestNeighborGraph :=
    ⟨Subtype.val, fun h => h⟩
  refine ⟨p.map f, ?_, ?_⟩
  · change p.length ≤ 2 * (Fintype.card s - 1) at hlen
    simpa only [SimpleGraph.Walk.length_map, Fintype.card_coe] using hlen
  · intro z
    rw [SimpleGraph.Walk.support_map, List.mem_map]
    constructor
    · rintro ⟨v, _, rfl⟩
      exact v.property
    · intro hz
      exact ⟨⟨z, hz⟩, hcover ⟨z, hz⟩, rfl⟩

/-- Neighboring lattice sites have coordinate changes of absolute value at most one. -/
theorem nearestNeighborGraph_adj_coordinate_bounds {x y : Lattice}
    (h : nearestNeighborGraph.Adj x y) :
    |y.1 - x.1| ≤ 1 ∧ |y.2 - x.2| ≤ 1 := by
  rcases h with h | h
  · rw [abs_sub_comm, h.1, h.2, sub_self, abs_zero]
    exact ⟨le_rfl, by omega⟩
  · rw [h.1, sub_self, abs_zero, abs_sub_comm, h.2]
    exact ⟨by omega, le_rfl⟩

/-- Reading a closed animal traversal at natural times, held at zero after it ends,
visits every animal site within the time window `0,...,2n`. -/
theorem exists_padded_animal_walk (s : Finset Lattice) (hs : IsConnectedAnimal s)
    (hzero : (0 : Lattice) ∈ s) :
    ∃ w : ℕ → Lattice, w 0 = 0 ∧
      (∀ t, |(w (t + 1)).1 - (w t).1| ≤ 1 ∧
        |(w (t + 1)).2 - (w t).2| ≤ 1) ∧
      (∀ z ∈ s, ∃ t ≤ 2 * s.card, w t = z) ∧
      (∀ t, w t ∈ s) := by
  obtain ⟨p, hlen, hsupport⟩ := exists_animal_traversal s hs hzero
  refine ⟨p.getVert, p.getVert_zero, ?_, ?_, ?_⟩
  · intro t
    by_cases ht : t < p.length
    · exact nearestNeighborGraph_adj_coordinate_bounds (p.adj_getVert_succ ht)
    · rw [p.getVert_of_length_le (by omega : p.length ≤ t),
        p.getVert_of_length_le (by omega : p.length ≤ t + 1)]
      simp only [sub_self, abs_zero, zero_le_one, and_self]
  · intro z hz
    obtain ⟨t, ht, htle⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp
      ((hsupport z).2 hz)
    exact ⟨t, by omega, ht⟩
  · intro t
    exact (hsupport _).1 (p.getVert_mem_support t)

end LPPDifferentiability
