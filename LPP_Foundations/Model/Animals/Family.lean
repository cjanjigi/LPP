/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Animals.WalkBounds
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Set.Finite.Basic
import Lean.Elab.Tactic.Omega

/-! The family of rooted animals of fixed size is finite and nonempty at every
positive size. No maximum is assigned to the empty size-zero family. -/

@[expose] public section

namespace LPPDifferentiability

/-- Martin's family of animals of size `n` containing the origin. -/
def animalFamily (n : ℕ) : Set (Finset Lattice) :=
  {s | IsConnectedAnimal s ∧ (0 : Lattice) ∈ s ∧ s.card = n}

/-- The rooted, connected, fixed-cardinality characterization. -/
theorem mem_animalFamily_iff (n : ℕ) (s : Finset Lattice) :
    s ∈ animalFamily n ↔ IsConnectedAnimal s ∧ (0 : Lattice) ∈ s ∧ s.card = n :=
  Iff.rfl

/-- The fixed-size family is a subset of the powerset of one finite box. -/
theorem animalFamily_finite (n : ℕ) : (animalFamily n).Finite := by
  apply ((integerBox (0 : Lattice) (n - 1)).powerset.finite_toSet).subset
  intro s hs
  apply Finset.mem_powerset.mpr
  obtain ⟨hconn, hzero, hcard⟩ := (mem_animalFamily_iff n s).mp hs
  simpa only [hcard] using animal_subset_integerBox s hconn hzero

/-- The `n` consecutive nonnegative horizontal lattice sites. -/
def horizontalAnimal (n : ℕ) : Finset Lattice :=
  (Finset.range n).image (fun k : ℕ => ((k : ℤ), (0 : ℤ)))

/-- Horizontal animal sites are exactly `(k,0)` for `0 ≤ k < n`. -/
theorem mem_horizontalAnimal_iff (n : ℕ) (z : Lattice) :
    z ∈ horizontalAnimal n ↔ ∃ k : ℕ, k < n ∧ ((k : ℤ), (0 : ℤ)) = z := by
  simp only [horizontalAnimal, Finset.mem_image, Finset.mem_range]

/-- Different horizontal coordinates give different sites, so no sites are lost. -/
theorem horizontalAnimal_card (n : ℕ) : (horizontalAnimal n).card = n := by
  rw [horizontalAnimal, Finset.card_image_of_injective, Finset.card_range]
  intro a b hab
  have hab' := congrArg Prod.fst hab
  change (a : ℤ) = (b : ℤ) at hab'
  exact_mod_cast hab'

/-- Every positive-length horizontal animal contains the origin. -/
theorem zero_mem_horizontalAnimal (n : ℕ) (hn : 0 < n) :
    (0 : Lattice) ∈ horizontalAnimal n :=
  (mem_horizontalAnimal_iff n 0).2 ⟨0, hn, rfl⟩

private theorem horizontalAnimal_reachable (n : ℕ) (hn : 0 < n) :
    ∀ k (hk : k < n),
      (nearestNeighborGraph.induce (↑(horizontalAnimal n) : Set Lattice)).Reachable
        ⟨0, zero_mem_horizontalAnimal n hn⟩
        ⟨((k : ℤ), (0 : ℤ)), (mem_horizontalAnimal_iff n _).2 ⟨k, hk, rfl⟩⟩ := by
  intro k
  induction k with
  | zero =>
    intro hk
    exact .rfl
  | succ k ih =>
    intro hk
    have hk' : k < n := by omega
    apply (ih hk').trans
    apply SimpleGraph.Adj.reachable
    change nearestNeighborGraph.Adj ((k : ℤ), (0 : ℤ)) (((k + 1 : ℕ) : ℤ), (0 : ℤ))
    left
    constructor
    · simp only [Nat.cast_add, Nat.cast_one, sub_add_cancel_left, abs_neg, abs_one]
    · rfl

/-- Consecutive horizontal sites form a connected induced graph. -/
theorem horizontalAnimal_isConnected (n : ℕ) (hn : 0 < n) :
    IsConnectedAnimal (horizontalAnimal n) := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).2
  refine ⟨⟨0, zero_mem_horizontalAnimal n hn⟩, ?_⟩
  rintro ⟨z, hz⟩
  obtain ⟨k, hk, rfl⟩ := (mem_horizontalAnimal_iff n z).mp hz
  exact horizontalAnimal_reachable n hn k hk

/-- A concrete member of the family at every positive size. -/
theorem horizontalAnimal_mem_animalFamily (n : ℕ) (hn : 0 < n) :
    horizontalAnimal n ∈ animalFamily n :=
  (mem_animalFamily_iff n _).2
    ⟨horizontalAnimal_isConnected n hn, zero_mem_horizontalAnimal n hn,
      horizontalAnimal_card n⟩

/-- The rooted animal family is nonempty for every size at least one. -/
theorem animalFamily_nonempty (n : ℕ) (hn : 1 ≤ n) : (animalFamily n).Nonempty :=
  ⟨horizontalAnimal n, horizontalAnimal_mem_animalFamily n hn⟩

/-- Size zero has no rooted animal; this does not define a maximum there. -/
theorem animalFamily_zero : animalFamily 0 = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro s hs
  obtain ⟨_, hzero, hcard⟩ := (mem_animalFamily_iff 0 s).mp hs
  have hempty : s = ∅ := Finset.card_eq_zero.mp hcard
  rw [hempty] at hzero
  exact Finset.notMem_empty 0 hzero

end LPPDifferentiability
