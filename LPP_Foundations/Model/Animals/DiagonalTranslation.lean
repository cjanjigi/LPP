/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Animals.Maximum
public import LPP_Foundations.Model.Animals.DiagonalFamily

/-! Lattice translations preserve adjacency, connected finite sets and signed animal
weights. These are deterministic helpers for the stationarity property (3.2) of
Martin (2002). -/

@[expose] public section

namespace LPPDifferentiability

/-- Translation preserves the nearest-neighbor relation. -/
theorem nearestNeighborGraph_adj_add_left_iff (a x y : Lattice) :
    nearestNeighborGraph.Adj (a + x) (a + y) ↔ nearestNeighborGraph.Adj x y := by
  simp only [nearestNeighborGraph, Prod.fst_add, Prod.snd_add,
    add_sub_add_left_eq_sub, add_right_inj]

/-- A lattice translation loses no sites in a finite image. -/
theorem card_image_lattice_add (a : Lattice) (s : Finset Lattice) :
    (s.image (fun z => a + z)).card = s.card :=
  Finset.card_image_of_injective s (add_right_injective a)

/-- Translation by the negative vector gives the inverse of the translated finite set. -/
theorem image_lattice_neg_add_image (a : Lattice) (s : Finset Lattice) :
    (s.image (fun z => a + z)).image (fun z => -a + z) = s := by
  simp only [Finset.image_image, Function.comp_def, neg_add_cancel_left,
    Finset.image_id']

/-- Membership at a translated site is equivalent to original membership. -/
theorem add_mem_image_lattice_add_iff (a z : Lattice) (s : Finset Lattice) :
    a + z ∈ s.image (fun x => a + x) ↔ z ∈ s := by
  simp only [Finset.mem_image, add_right_inj, exists_eq_right]

/-- A translate of a connected set is connected. -/
theorem IsConnectedAnimal.image_lattice_add {s : Finset Lattice}
    (hs : IsConnectedAnimal s) (a : Lattice) :
    IsConnectedAnimal (s.image (fun z => a + z)) := by
  let f : nearestNeighborGraph.induce (↑s : Set Lattice) →g
      nearestNeighborGraph.induce (↑(s.image (fun z => a + z)) : Set Lattice) :=
    { toFun := fun z => ⟨a + z.val, Finset.mem_image.mpr ⟨z.val, z.property, rfl⟩⟩
      map_rel' := by
        intro x y hxy
        exact (nearestNeighborGraph_adj_add_left_iff a x.val y.val).2 hxy }
  apply SimpleGraph.Connected.map f ?_ hs
  rintro ⟨y, hy⟩
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  exact ⟨⟨x, hx⟩, rfl⟩

/-- Connectivity is equivalent before and after lattice translation. -/
theorem isConnectedAnimal_image_lattice_add_iff (a : Lattice) (s : Finset Lattice) :
    IsConnectedAnimal (s.image (fun z => a + z)) ↔ IsConnectedAnimal s := by
  constructor
  · intro hs
    have h := hs.image_lattice_add (-a)
    rw [image_lattice_neg_add_image] at h
    exact h
  · intro hs
    exact hs.image_lattice_add a

/-- Reindexing the translated finite set works for signed fields. -/
theorem animalWeight_image_lattice_add (a : Lattice) (s : Finset Lattice)
    (w : Lattice → ℝ) :
    animalWeight w (s.image (fun z => a + z)) =
      animalWeight (fun z => w (a + z)) s := by
  classical
  unfold animalWeight
  apply Finset.sum_image
  intro x _ y _ h
  exact add_left_cancel h

/-- Diagonal translation carries every member of the family to a member of the family
with both signed endpoints shifted by the same integer. -/
theorem image_mem_diagonalAnimalFamily {m n : ℤ} {s : Finset Lattice}
    (hs : s ∈ diagonalAnimalFamily m n) (k : ℤ) :
    s.image (fun z => (k, k) + z) ∈ diagonalAnimalFamily (m + k) (n + k) := by
  obtain ⟨hconn, hcard, hbox, hstart, ⟨z, hz, hadj⟩, hfinish⟩ :=
    (mem_diagonalAnimalFamily_iff m n s).mp hs
  have hstart_eq : (k, k) + (m, m) = (m + k, m + k) := by
    apply Prod.ext <;> exact add_comm k m
  have hfinish_eq : (k, k) + (n, n) = (n + k, n + k) := by
    apply Prod.ext <;> exact add_comm k n
  refine (mem_diagonalAnimalFamily_iff _ _ _).2
    ⟨hconn.image_lattice_add (k, k), ?_, ?_, ?_, ?_, ?_⟩
  · rw [card_image_lattice_add]
    have hdelta : n + k - (m + k) = n - m := by omega
    rw [hdelta]
    exact hcard
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hx₁, hx₂⟩ := Finset.mem_product.mp (hbox hx)
    obtain ⟨hm₁, hn₁⟩ := Finset.mem_Icc.mp hx₁
    obtain ⟨hm₂, hn₂⟩ := Finset.mem_Icc.mp hx₂
    apply Finset.mem_product.mpr
    constructor <;> apply Finset.mem_Icc.mpr <;>
      dsimp only [Prod.fst_add, Prod.snd_add] <;> constructor <;> omega
  · rw [← hstart_eq]
    exact Finset.mem_image_of_mem _ hstart
  · refine ⟨(k, k) + z, Finset.mem_image_of_mem _ hz, ?_⟩
    rw [← hfinish_eq]
    exact (nearestNeighborGraph_adj_add_left_iff (k, k) z (n, n)).2 hadj
  · rw [← hfinish_eq, add_mem_image_lattice_add_iff]
    exact hfinish

/-- Membership in Martin's family is preserved by diagonal translation in both
directions; the converse uses the negative translation. -/
theorem image_mem_diagonalAnimalFamily_iff (m n k : ℤ) (s : Finset Lattice) :
    s.image (fun z => (k, k) + z) ∈ diagonalAnimalFamily (m + k) (n + k) ↔
      s ∈ diagonalAnimalFamily m n := by
  constructor
  · intro hs
    have h := image_mem_diagonalAnimalFamily hs (-k)
    have hinv : (s.image (fun z => (k, k) + z)).image
        (fun z => (-k, -k) + z) = s :=
      image_lattice_neg_add_image (k, k) s
    rw [hinv, add_neg_cancel_right, add_neg_cancel_right] at h
    exact h
  · intro hs
    exact image_mem_diagonalAnimalFamily hs k

end LPPDifferentiability
