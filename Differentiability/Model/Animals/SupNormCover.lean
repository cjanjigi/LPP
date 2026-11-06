/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Animals.Traversal
import Mathlib.Data.Finset.Card

/-! A finite radius-one connected set has a nearest-neighbor cover of size
at most twice its cardinality. Tree growth inserts one coordinate corner
for each attachment edge. -/

public section

namespace LPPDifferentiability

private theorem walk_preserves_predicate {V : Type*} {G : SimpleGraph V}
    (P : V → Prop) (hc : ∀ x, P x → ∀ y, G.Adj x y → P y)
    {x y : V} (p : G.Walk x y) (hx : P x) : P y := by
  induction p with
  | nil => exact hx
  | @cons x z y hxz p ih => exact ih (hc x hx z hxz)

private theorem exists_crossing {V : Type*} {G : SimpleGraph V}
    (hG : G.Connected) (P : V → Prop) (a b : V) (ha : P a) (hb : ¬ P b) :
    ∃ x, P x ∧ ∃ y, ¬ P y ∧ G.Adj x y := by
  classical
  by_contra hn
  push Not at hn
  have hc : ∀ x, P x → ∀ y, G.Adj x y → P y := by
    intro x hx y hxy
    by_contra hy
    exact hn x hx y hy hxy
  obtain ⟨p⟩ := hG.preconnected a b
  exact hb (walk_preserves_predicate P hc p ha)

private theorem animal_insert {B : Finset Lattice} (hB : IsConnectedAnimal B)
    {x y : Lattice} (hx : x ∈ B)
    (hxy : x = y ∨ nearestNeighborGraph.Adj x y) :
    IsConnectedAnimal (insert y B) := by
  classical
  rcases hxy with rfl | hxy
  · simpa only [Finset.insert_eq_of_mem hx] using hB
  let f : nearestNeighborGraph.induce (↑B : Set Lattice) →g
      nearestNeighborGraph.induce (↑(insert y B) : Set Lattice) :=
    ⟨fun z => ⟨z.val, Finset.mem_insert_of_mem z.property⟩, fun h => h⟩
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).2
  refine ⟨⟨x, Finset.mem_insert_of_mem hx⟩, ?_⟩
  rintro ⟨z, hz⟩
  rcases Finset.mem_insert.mp hz with rfl | hz
  · exact SimpleGraph.Adj.reachable hxy
  · exact (hB.preconnected (⟨x, hx⟩ : B) ⟨z, hz⟩).map f

private theorem corner_steps (x y : Lattice)
    (h₁ : |x.1 - y.1| ≤ 1) (h₂ : |x.2 - y.2| ≤ 1) :
    (x = (x.1, y.2) ∨ nearestNeighborGraph.Adj x (x.1, y.2)) ∧
    ((x.1, y.2) = y ∨ nearestNeighborGraph.Adj (x.1, y.2) y) := by
  have hx := abs_le.mp h₁
  have hy := abs_le.mp h₂
  constructor
  · by_cases he : x.2 = y.2
    · left; exact Prod.ext rfl he
    · right; right
      refine ⟨rfl, ?_⟩
      change |x.2 - y.2| = 1
      have hd : x.2 - y.2 = 1 ∨ x.2 - y.2 = -1 := by omega
      rcases hd with hd | hd <;> simp only [hd, abs_neg, abs_one]
  · by_cases he : x.1 = y.1
    · left; exact Prod.ext he rfl
    · right; left
      refine ⟨?_, rfl⟩
      change |x.1 - y.1| = 1
      have hd : x.1 - y.1 = 1 ∨ x.1 - y.1 = -1 := by omega
      rcases hd with hd | hd <;> simp only [hd, abs_neg, abs_one]

/-- A finite radius-one connected set admits a nearest-neighbor animal cover.
The distinguished point need not be the origin. -/
theorem exists_supNorm_animal_cover (A : Finset Lattice) (o : Lattice) (ho : o ∈ A)
    (hA : ((SimpleGraph.fromRel (fun x y : Lattice =>
      |x.1 - y.1| ≤ 1 ∧ |x.2 - y.2| ≤ 1)).induce (↑A : Set Lattice)).Connected) :
    ∃ B : Finset Lattice, A ⊆ B ∧ o ∈ B ∧ IsConnectedAnimal B ∧
      B.card + 1 ≤ 2 * A.card := by
  classical
  have grow : ∀ n : ℕ, n + 1 ≤ A.card →
      ∃ S B : Finset Lattice, S ⊆ A ∧ o ∈ S ∧ S.card = n + 1 ∧
        S ⊆ B ∧ IsConnectedAnimal B ∧ B.card + 1 ≤ 2 * S.card := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨{o}, {o}, Finset.singleton_subset_iff.mpr ho,
        Finset.mem_singleton_self o, Finset.card_singleton o,
        Finset.Subset.refl _, ?_, by simp only [Finset.card_singleton]; omega⟩
      apply (SimpleGraph.connected_iff_exists_forall_reachable _).2
      refine ⟨⟨o, Finset.mem_singleton_self o⟩, ?_⟩
      rintro ⟨z, hz⟩
      have he : z = o := Finset.mem_singleton.mp hz
      subst z
      exact SimpleGraph.Reachable.rfl
    | succ n ih =>
      intro hn
      obtain ⟨S, B, hSA, hoS, hScard, hSB, hB, hBcard⟩ := ih (by omega)
      obtain ⟨y, hyA, hyS⟩ : ∃ y ∈ A, y ∉ S := by
        by_contra hh
        push Not at hh
        have hAS : A ⊆ S := hh
        have := Finset.card_le_card hAS
        omega
      obtain ⟨x, hxS, y, hyS, hxy⟩ := exists_crossing hA
        (fun z : A => z.val ∈ S) ⟨o, ho⟩ ⟨y, hyA⟩ hoS hyS
      have hrel : |x.val.1 - y.val.1| ≤ 1 ∧ |x.val.2 - y.val.2| ≤ 1 := by
        change x.val ≠ y.val ∧
          ((|x.val.1 - y.val.1| ≤ 1 ∧ |x.val.2 - y.val.2| ≤ 1) ∨
          (|y.val.1 - x.val.1| ≤ 1 ∧ |y.val.2 - x.val.2| ≤ 1)) at hxy
        rcases hxy.2 with h | h
        · exact h
        · simpa only [abs_sub_comm] using h
      let c : Lattice := (x.val.1, y.val.2)
      obtain ⟨hxc, hcy⟩ := corner_steps x.val y.val hrel.1 hrel.2
      have hBc : IsConnectedAnimal (insert c B) := animal_insert hB (hSB hxS) hxc
      have hBy : IsConnectedAnimal (insert y.val (insert c B)) :=
        animal_insert hBc (Finset.mem_insert_self c B) hcy
      refine ⟨insert y.val S, insert y.val (insert c B), ?_,
        Finset.mem_insert_of_mem hoS, ?_, ?_, hBy, ?_⟩
      · exact Finset.insert_subset y.property hSA
      · rw [Finset.card_insert_of_notMem hyS, hScard]
      · intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hSB hz))
      · have hc := Finset.card_insert_le c B
        have hy := Finset.card_insert_le y.val (insert c B)
        rw [Finset.card_insert_of_notMem hyS]
        omega
  have hpos : 0 < A.card := Finset.card_pos.mpr ⟨o, ho⟩
  obtain ⟨S, B, hSA, hoS, hScard, hSB, hB, hBcard⟩ :=
    grow (A.card - 1) (by omega)
  have hSAeq : S = A := Finset.eq_of_subset_of_card_le hSA (by omega)
  exact ⟨B, hSAeq ▸ hSB, hSB hoS, hB, by omega⟩

end LPPDifferentiability
