/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Animals.DiagonalMaximum
public import LPP_Foundations.Model.Animals.DiagonalGluing
public import LPP_Foundations.Model.Animals.Extension
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega

/-! Two planar comparisons between the diagonal maximum and rooted animal maxima,
for nonnegative site fields: Martin (2002), Lemma 3.1. -/

@[expose] public section

namespace LPPDifferentiability

/-- Enlarging a finite set increases its weight for a nonnegative site field. -/
theorem animalWeight_mono_of_subset (w : Lattice → ℝ) (hw : ∀ z, 0 ≤ w z)
    {s t : Finset Lattice} (hst : s ⊆ t) : animalWeight w s ≤ animalWeight w t := by
  unfold animalWeight
  exact Finset.sum_le_sum_of_subset_of_nonneg hst (fun z _ _ => hw z)

/-- Martin (2002), Lemma 3.1(i): extend each feasible diagonal animal to size exactly `3n`. -/
theorem diagonalAnimalMaximum_zero_le_animalMaximum (n : ℕ) (hn : 1 ≤ n)
    (w : Lattice → ℝ) (hw : ∀ z, 0 ≤ w z) :
    diagonalAnimalMaximum 0 (n : ℤ) (by omega) w ≤
      animalMaximum (3 * n) (by omega) w := by
  apply (diagonalAnimalMaximum_le_iff 0 n (by omega) w _).2
  intro s hs
  obtain ⟨hconn, hcard, _, hzero, _, _⟩ :=
    (mem_diagonalAnimalFamily_iff 0 n s).mp hs
  have hcard' : s.card ≤ 3 * n := by simpa only [sub_zero, Int.toNat_natCast] using hcard
  obtain ⟨t, ht, hst⟩ := hconn.exists_extension_mem_animalFamily hzero (3 * n) hcard'
  exact (animalWeight_mono_of_subset w hw hst).trans
    (animalWeight_le_animalMaximum (3 * n) (by omega) w ht)

/-- The terminal-excluded connector is the union of two consecutive paths,
with zero kept at their join and exactly `4n` sites. -/
theorem exists_diagonal_connector (n : ℕ) (hn : 1 ≤ n) :
    ∃ c ∈ diagonalAnimalFamily (-(n : ℤ)) (n : ℤ),
      c.card = 4 * n ∧ (0 : Lattice) ∈ c := by
  let p := horizontalFirst (-(n : ℤ), -(n : ℤ))
    ((0 - -(n : ℤ)).toNat, (0 - -(n : ℤ)).toNat)
  let q := horizontalFirst (0 : Lattice) (((n : ℤ) - 0).toNat, ((n : ℤ) - 0).toNat)
  have hp : p.collectedSites ∈ diagonalAnimalFamily (-(n : ℤ)) 0 :=
    Path.collectedSites_mem_diagonalAnimalFamily (-(n : ℤ)) 0 (by omega) p
  have hq : q.collectedSites ∈ diagonalAnimalFamily 0 (n : ℤ) :=
    Path.collectedSites_mem_diagonalAnimalFamily 0 (n : ℤ) (by omega) q
  refine ⟨p.collectedSites ∪ q.collectedSites,
    diagonalAnimalFamily_union (by omega) (by omega) hp hq, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint (diagonalAnimalFamily_disjoint hp hq),
      p.collectedSites_card, q.collectedSites_card]
    dsimp only [p, q]
    simp only [sub_neg_eq_add, zero_add, sub_zero, Int.toNat_natCast]
    omega
  · exact Finset.mem_union_right _
      ((mem_diagonalAnimalFamily_iff 0 (n : ℤ) _).mp hq).2.2.2.1

/-- A rooted size-`n` animal is inside the diagonal cube and excludes its
positive terminal corner, since its radius is at most `n-1`. -/
theorem animalFamily_subset_diagonal_cube {n : ℕ} (hn : 1 ≤ n)
    {s : Finset Lattice} (hs : s ∈ animalFamily n) :
    s ⊆ (Finset.Icc (-(n : ℤ)) (n : ℤ)) ×ˢ (Finset.Icc (-(n : ℤ)) (n : ℤ)) ∧
      ((n : ℤ), (n : ℤ)) ∉ s := by
  obtain ⟨hconn, hzero, hcard⟩ := (mem_animalFamily_iff n s).mp hs
  have hbounds (z : Lattice) (hz : z ∈ s) :
      |z.1| ≤ ((n - 1 : ℕ) : ℤ) ∧ |z.2| ≤ ((n - 1 : ℕ) : ℤ) := by
    have hbox := animal_subset_integerBox s hconn hzero hz
    have h := (mem_integerBox_iff 0 z (s.card - 1)).mp hbox
    simpa only [hcard, Prod.fst_zero, Prod.snd_zero, sub_zero] using h
  constructor
  · intro z hz
    obtain ⟨hx, hy⟩ := hbounds z hz
    rw [abs_le] at hx hy
    exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
       Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
  · intro hz
    have hx := (hbounds ((n : ℤ), (n : ℤ)) hz).1
    have hnnonneg : (0 : ℤ) ≤ (n : ℤ) := by omega
    rw [abs_of_nonneg hnnonneg] at hx
    omega

/-- Every rooted animal extends, through the connector, to a member of the diagonal
family. The connector is constructed here, not assumed as a premise. -/
theorem exists_diagonalAnimalFamily_superset {n : ℕ} (hn : 1 ≤ n)
    {s : Finset Lattice} (hs : s ∈ animalFamily n) :
    ∃ t ∈ diagonalAnimalFamily (-(n : ℤ)) (n : ℤ), s ⊆ t := by
  obtain ⟨c, hc, hccard, hczero⟩ := exists_diagonal_connector n hn
  obtain ⟨hsconn, hszero, hscard⟩ := (mem_animalFamily_iff n s).mp hs
  obtain ⟨hcconn, _, hcbox, hcstart, hcnear, hcend⟩ :=
    (mem_diagonalAnimalFamily_iff (-(n : ℤ)) n c).mp hc
  obtain ⟨hsbox, hsend⟩ := animalFamily_subset_diagonal_cube hn hs
  refine ⟨s ∪ c, (mem_diagonalAnimalFamily_iff (-(n : ℤ)) n _).2
    ⟨?_, ?_, Finset.union_subset hsbox hcbox, Finset.mem_union_right _ hcstart,
      ?_, ?_⟩, Finset.subset_union_left⟩
  · unfold IsConnectedAnimal at hsconn hcconn ⊢
    rw [Finset.coe_union]
    exact SimpleGraph.induce_union_connected hsconn.preconnected hcconn.preconnected
      ⟨0, hszero, hczero⟩
  · have hcard := Finset.card_union_le s c
    rw [hscard, hccard] at hcard
    have hlength : ((n : ℤ) - -(n : ℤ)).toNat = 2 * n := by omega
    rw [hlength]
    omega
  · obtain ⟨z, hz, hzad⟩ := hcnear
    exact ⟨z, Finset.mem_union_right _ hz, hzad⟩
  · intro hz
    exact (Finset.notMem_union.mpr ⟨hsend, hcend⟩) hz

/-- Martin (2002), Lemma 3.1(ii): add the path through zero, then use nonnegative weights. -/
theorem animalMaximum_le_diagonalAnimalMaximum (n : ℕ) (hn : 1 ≤ n)
    (w : Lattice → ℝ) (hw : ∀ z, 0 ≤ w z) :
    animalMaximum n hn w ≤
      diagonalAnimalMaximum (-(n : ℤ)) (n : ℤ) (by omega) w := by
  apply (animalMaximum_le_iff n hn w _).2
  intro s hs
  obtain ⟨t, ht, hst⟩ := exists_diagonalAnimalFamily_superset hn hs
  exact (animalWeight_mono_of_subset w hw hst).trans
    (diagonalAnimalWeight_le_diagonalAnimalMaximum (-(n : ℤ)) n (by omega) w ht)

end LPPDifferentiability
