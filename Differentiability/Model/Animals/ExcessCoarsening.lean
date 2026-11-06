/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.Animals.SupNormCover

/-! Signed Euclidean coarsening of a radius-two connected set, and its nearest-neighbor
animal cover with factor two. -/

public section

namespace LPPDifferentiability

/-- The signed quotients contract radius two to radius one. -/
theorem excess_coarsening_coordinate_bounds (x y : Lattice) (α β : ℤ)
    (h₁ : |x.1 - y.1| ≤ 2) (h₂ : |x.2 - y.2| ≤ 2) :
    |(x.1 - α) / 4 - (y.1 - α) / 4| ≤ 1 ∧
      |(x.2 - β) / 10 - (y.2 - β) / 10| ≤ 1 := by
  have hx := abs_le.mp h₁
  have hy := abs_le.mp h₂
  constructor
  · apply abs_le.mpr
    constructor <;> omega
  · apply abs_le.mpr
    constructor <;> omega

private theorem map_walk_reachable {V W : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} (f : V → W)
    (hf : ∀ x y, G.Adj x y → f x = f y ∨ H.Adj (f x) (f y))
    {x y : V} (p : G.Walk x y) : H.Reachable (f x) (f y) := by
  induction p with
  | nil => exact SimpleGraph.Reachable.rfl
  | @cons x z y hxz p ih =>
    rcases hf x z hxz with he | ha
    · rw [he]
      exact ih
    · exact ha.reachable.trans ih

/-- Collapsed consecutive images are handled as reflexive reachable steps.
No connectedness of the image is assumed. -/
theorem excess_coarsening_image_connected (A : Finset Lattice) (α β : ℤ)
    (hA : ((SimpleGraph.fromRel (fun x y : Lattice =>
      |x.1 - y.1| ≤ 2 ∧ |x.2 - y.2| ≤ 2)).induce (↑A : Set Lattice)).Connected) :
    ((SimpleGraph.fromRel (fun x y : Lattice =>
      |x.1 - y.1| ≤ 1 ∧ |x.2 - y.2| ≤ 1)).induce
        (↑(A.image (fun z => ((z.1 - α) / 4, (z.2 - β) / 10))) : Set Lattice)).Connected := by
  classical
  let ψ : Lattice → Lattice := fun z => ((z.1 - α) / 4, (z.2 - β) / 10)
  let C := A.image ψ
  let G := (SimpleGraph.fromRel (fun x y : Lattice =>
    |x.1 - y.1| ≤ 2 ∧ |x.2 - y.2| ≤ 2)).induce (↑A : Set Lattice)
  let H := (SimpleGraph.fromRel (fun x y : Lattice =>
    |x.1 - y.1| ≤ 1 ∧ |x.2 - y.2| ≤ 1)).induce (↑C : Set Lattice)
  let f : A → C := fun z => ⟨ψ z.val, Finset.mem_image.mpr ⟨z.val, z.property, rfl⟩⟩
  have hf : ∀ x y : A, G.Adj x y → f x = f y ∨ H.Adj (f x) (f y) := by
    intro x y hxy
    have hrel : |x.val.1 - y.val.1| ≤ 2 ∧ |x.val.2 - y.val.2| ≤ 2 := by
      change x.val ≠ y.val ∧
        ((|x.val.1 - y.val.1| ≤ 2 ∧ |x.val.2 - y.val.2| ≤ 2) ∨
        (|y.val.1 - x.val.1| ≤ 2 ∧ |y.val.2 - x.val.2| ≤ 2)) at hxy
      rcases hxy.2 with h | h
      · exact h
      · simpa only [abs_sub_comm] using h
    have hb := excess_coarsening_coordinate_bounds x.val y.val α β hrel.1 hrel.2
    by_cases he : ψ x.val = ψ y.val
    · left; exact Subtype.ext he
    · right
      change ψ x.val ≠ ψ y.val ∧ _
      exact ⟨he, Or.inl hb⟩
  obtain ⟨a⟩ := hA.nonempty
  change H.Connected
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).2
  refine ⟨f a, ?_⟩
  rintro ⟨z, hz⟩
  obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hz
  have he' : f (⟨y, hy⟩ : A) = (⟨z, hz⟩ : C) := Subtype.ext he
  obtain ⟨p⟩ := hA.preconnected a (⟨y, hy⟩ : A)
  exact he' ▸ map_walk_reachable f hf p

/-- Produce an animal that contains the signed coarsening image and the given point,
keeping the exact factor two. -/
theorem exists_excess_coarsening_animal_cover (A : Finset Lattice)
    (o : Lattice) (ho : o ∈ A) (α β : ℤ)
    (hA : ((SimpleGraph.fromRel (fun x y : Lattice =>
      |x.1 - y.1| ≤ 2 ∧ |x.2 - y.2| ≤ 2)).induce (↑A : Set Lattice)).Connected) :
    ∃ B : Finset Lattice,
      A.image (fun z => ((z.1 - α) / 4, (z.2 - β) / 10)) ⊆ B ∧
      ((o.1 - α) / 4, (o.2 - β) / 10) ∈ B ∧ IsConnectedAnimal B ∧
      B.card + 1 ≤ 2 * A.card := by
  classical
  let ψ : Lattice → Lattice := fun z => ((z.1 - α) / 4, (z.2 - β) / 10)
  have himg : ψ o ∈ A.image ψ := Finset.mem_image.mpr ⟨o, ho, rfl⟩
  have hconn := excess_coarsening_image_connected A α β hA
  obtain ⟨B, hsub, hpoint, hB, hcard⟩ :=
    exists_supNorm_animal_cover (A.image ψ) (ψ o) himg hconn
  have hsize : (A.image ψ).card ≤ A.card := Finset.card_image_le
  exact ⟨B, hsub, hpoint, hB, by omega⟩

end LPPDifferentiability
