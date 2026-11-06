/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Animals.Maximum
public import LPP_Foundations.Model.Animals.DiagonalFamily
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Data.Finset.Prod
import Lean.Elab.Tactic.Omega

/-! The geometric and weight steps in Martin's diagonal animal gluing. -/

@[expose] public section

namespace LPPDifferentiability

/-- The closed diagonal cubes on successive intervals meet only at their
common diagonal endpoint. -/
theorem diagonal_cubes_intersection {l m n : ℤ} {z : Lattice}
    (hs : z ∈ (Finset.Icc l m) ×ˢ (Finset.Icc l m))
    (ht : z ∈ (Finset.Icc m n) ×ˢ (Finset.Icc m n)) : z = (m, m) := by
  obtain ⟨hx, hy⟩ := Finset.mem_product.mp hs
  obtain ⟨hx', hy'⟩ := Finset.mem_product.mp ht
  obtain ⟨_, hxm⟩ := Finset.mem_Icc.mp hx
  obtain ⟨_, hym⟩ := Finset.mem_Icc.mp hy
  obtain ⟨hmx, _⟩ := Finset.mem_Icc.mp hx'
  obtain ⟨hmy, _⟩ := Finset.mem_Icc.mp hy'
  exact Prod.ext (le_antisymm hxm hmx) (le_antisymm hym hmy)

/-- Excluding the common endpoint makes animals in successive closed cubes
disjoint. No sign restriction on a later site field is involved. -/
theorem disjoint_of_diagonal_cubes {l m n : ℤ} {s t : Finset Lattice}
    (hs : s ⊆ (Finset.Icc l m) ×ˢ (Finset.Icc l m))
    (ht : t ⊆ (Finset.Icc m n) ×ˢ (Finset.Icc m n))
    (hm : (m, m) ∉ s) : Disjoint s t := by
  apply Finset.disjoint_left.mpr
  intro z hzs hzt
  have hz := diagonal_cubes_intersection (hs hzs) (ht hzt)
  exact hm (hz ▸ hzs)

/-- An edge between two connected animals connects their union. -/
theorem IsConnectedAnimal.union_of_adj {s t : Finset Lattice}
    (hs : IsConnectedAnimal s) (ht : IsConnectedAnimal t)
    {x y : Lattice} (hx : x ∈ s) (hy : y ∈ t)
    (hxy : nearestNeighborGraph.Adj x y) : IsConnectedAnimal (s ∪ t) := by
  unfold IsConnectedAnimal at hs ht ⊢
  rw [Finset.coe_union]
  exact SimpleGraph.connected_induce_union hs.preconnected ht.preconnected hx hy hxy

/-- Weight is exactly additive on disjoint animals, including signed fields. -/
theorem animalWeight_union_of_disjoint (w : Lattice → ℝ) {s t : Finset Lattice}
    (h : Disjoint s t) : animalWeight w (s ∪ t) = animalWeight w s + animalWeight w t := by
  unfold animalWeight
  exact Finset.sum_union h

/-- Members of consecutive diagonal families are disjoint. -/
theorem diagonalAnimalFamily_disjoint {l m n : ℤ} {s t : Finset Lattice}
    (hs : s ∈ diagonalAnimalFamily l m) (ht : t ∈ diagonalAnimalFamily m n) :
    Disjoint s t := by
  obtain ⟨_, _, hsbox, _, _, hsend⟩ := (mem_diagonalAnimalFamily_iff l m s).mp hs
  obtain ⟨_, _, htbox, _, _, _⟩ := (mem_diagonalAnimalFamily_iff m n t).mp ht
  exact disjoint_of_diagonal_cubes hsbox htbox hsend

/-- Gluing animals from consecutive intervals gives a member of the longer diagonal
family. Every condition is derived from the two memberships. -/
theorem diagonalAnimalFamily_union {l m n : ℤ} (hlm : l < m) (hmn : m < n)
    {s t : Finset Lattice} (hs : s ∈ diagonalAnimalFamily l m)
    (ht : t ∈ diagonalAnimalFamily m n) : s ∪ t ∈ diagonalAnimalFamily l n := by
  have hdisj := diagonalAnimalFamily_disjoint hs ht
  obtain ⟨hsconn, hscard, hsbox, hsstart, hsnear, _⟩ :=
    (mem_diagonalAnimalFamily_iff l m s).mp hs
  obtain ⟨htconn, htcard, htbox, htstart, htnear, htend⟩ :=
    (mem_diagonalAnimalFamily_iff m n t).mp ht
  refine (mem_diagonalAnimalFamily_iff l n _).2
    ⟨?_, ?_, ?_, Finset.mem_union_left _ hsstart, ?_, ?_⟩
  · obtain ⟨z, hz, hzad⟩ := hsnear
    exact hsconn.union_of_adj htconn hz htstart hzad
  · rw [Finset.card_union_of_disjoint hdisj]
    have hlength : (m - l).toNat + (n - m).toNat = (n - l).toNat := by omega
    omega
  · intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨hx, hy⟩ := Finset.mem_product.mp (hsbox hz)
      obtain ⟨hlx, hxm⟩ := Finset.mem_Icc.mp hx
      obtain ⟨hly, hym⟩ := Finset.mem_Icc.mp hy
      exact Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr ⟨hlx, hxm.trans hmn.le⟩,
         Finset.mem_Icc.mpr ⟨hly, hym.trans hmn.le⟩⟩
    · obtain ⟨hx, hy⟩ := Finset.mem_product.mp (htbox hz)
      obtain ⟨hmx, hxn⟩ := Finset.mem_Icc.mp hx
      obtain ⟨hmy, hyn⟩ := Finset.mem_Icc.mp hy
      exact Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr ⟨hlm.le.trans hmx, hxn⟩,
         Finset.mem_Icc.mpr ⟨hlm.le.trans hmy, hyn⟩⟩
  · obtain ⟨z, hz, hzad⟩ := htnear
    exact ⟨z, Finset.mem_union_right _ hz, hzad⟩
  · intro hn
    rcases Finset.mem_union.mp hn with hn | hn
    · have hnm := (Finset.mem_Icc.mp (Finset.mem_product.mp (hsbox hn)).1).2
      omega
    · exact htend hn

/-- Consecutive diagonal animals have exactly additive weight for arbitrary
real site fields; disjointness is derived from their membership in the family. -/
theorem animalWeight_union_of_mem_diagonalAnimalFamily (w : Lattice → ℝ)
    {l m n : ℤ} {s t : Finset Lattice} (hs : s ∈ diagonalAnimalFamily l m)
    (ht : t ∈ diagonalAnimalFamily m n) :
    animalWeight w (s ∪ t) = animalWeight w s + animalWeight w t :=
  animalWeight_union_of_disjoint w (diagonalAnimalFamily_disjoint hs ht)

end LPPDifferentiability
