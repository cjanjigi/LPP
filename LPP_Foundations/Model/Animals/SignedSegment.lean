/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Animals.Extension
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Tactic

/-! A signed coordinate segment lies in a rooted animal of linear size. -/

@[expose] public section

namespace LPPDifferentiability

private theorem unit_ray (u d : Lattice)
    (hd : ∀ v : Lattice, nearestNeighborGraph.Adj v (v + d)) (n : ℕ) :
    ∃ p : nearestNeighborGraph.Walk u (u + (n : ℤ) • d),
      p.length = n ∧ ∀ k : ℕ, k ≤ n → u + (k : ℤ) • d ∈ p.support := by
  induction n with
  | zero =>
    let p : nearestNeighborGraph.Walk u (u + (0 : ℤ) • d) :=
      (SimpleGraph.Walk.nil : nearestNeighborGraph.Walk u u).copy rfl (by simp)
    refine ⟨p, ?_, ?_⟩
    · simp [p]
    · intro k hk
      have : k = 0 := by omega
      subst k
      simp [p]
  | succ n ih =>
    obtain ⟨p, hp, hmem⟩ := ih
    have hend : u + ((n + 1 : ℕ) : ℤ) • d = (u + (n : ℤ) • d) + d := by
      simp only [Nat.cast_add, Nat.cast_one, add_zsmul, one_zsmul, add_assoc]
    let q := p.concat (hd (u + (n : ℤ) • d))
    let hq : nearestNeighborGraph.Walk u (u + ((n + 1 : ℕ) : ℤ) • d) :=
      q.copy rfl hend.symm
    refine ⟨hq, ?_, ?_⟩
    · simpa [hq, q] using congrArg (fun t : ℕ => t + 1) hp
    · intro k hk
      by_cases hk' : k ≤ n
      · have h := hmem k hk'
        simpa [hq, q] using (SimpleGraph.Walk.support_subset_support_concat p
          (hd (u + (n : ℤ) • d)) h)
      · have hkEq : k = n + 1 := by omega
        subst k
        exact hq.end_mem_support

private theorem east_adj (v : Lattice) : nearestNeighborGraph.Adj v (v + (1, 0)) := by
  left
  simp

private theorem west_adj (v : Lattice) : nearestNeighborGraph.Adj v (v + (-1, 0)) := by
  left
  simp

private theorem north_adj (v : Lattice) : nearestNeighborGraph.Adj v (v + (0, 1)) := by
  right
  simp

private theorem south_adj (v : Lattice) : nearestNeighborGraph.Adj v (v + (0, -1)) := by
  right
  simp

private theorem horizontal_walk (u : Lattice) (z : ℤ) :
    ∃ p : nearestNeighborGraph.Walk u (u + (z, 0)), p.length = z.natAbs := by
  cases z with
  | ofNat n =>
    obtain ⟨p, hp, _⟩ := unit_ray u (1, 0) east_adj n
    have he : u + (n : ℤ) • ((1, 0) : Lattice) = u + ((n : ℤ), 0) := by simp
    exact ⟨p.copy rfl he, by simpa using hp⟩
  | negSucc n =>
    obtain ⟨p, hp, _⟩ := unit_ray u (-1, 0) west_adj (n + 1)
    have he : u + ((n + 1 : ℕ) : ℤ) • ((-1, 0) : Lattice) =
        u + (Int.negSucc n, 0) := by simp [Int.negSucc_eq]
    exact ⟨p.copy rfl he, by simpa using hp⟩

private theorem vertical_walk (u : Lattice) (z : ℤ) :
    ∃ p : nearestNeighborGraph.Walk u (u + (0, z)), p.length = z.natAbs := by
  cases z with
  | ofNat n =>
    obtain ⟨p, hp, _⟩ := unit_ray u (0, 1) north_adj n
    have he : u + (n : ℤ) • ((0, 1) : Lattice) = u + (0, (n : ℤ)) := by simp
    exact ⟨p.copy rfl he, by simpa using hp⟩
  | negSucc n =>
    obtain ⟨p, hp, _⟩ := unit_ray u (0, -1) south_adj (n + 1)
    have he : u + ((n + 1 : ℕ) : ℤ) • ((0, -1) : Lattice) =
        u + (0, Int.negSucc n) := by simp [Int.negSucc_eq]
    exact ⟨p.copy rfl he, by simpa using hp⟩

/-- A signed coordinate segment is contained in an animal of any sufficiently
large prescribed size. This is the finite geometry used in the animal weight input. -/
theorem exists_animalFamily_containing_signed_coordinate_segment
    (x : Lattice) (i : Fin 2) (m N : ℕ)
    (hN : x.1.natAbs + x.2.natAbs + m + 1 ≤ N) :
    ∃ A : Finset Lattice, A ∈ animalFamily N ∧
      ∀ k : ℕ, k ≤ m →
        x + (k : ℤ) • (if i = 0 then ((1 : ℤ), (0 : ℤ))
          else ((0 : ℤ), (1 : ℤ))) ∈ A := by
  classical
  let d : Lattice := if i = 0 then (1, 0) else (0, 1)
  have hd : ∀ v : Lattice, nearestNeighborGraph.Adj v (v + d) := by
    intro v
    by_cases hi : i = 0
    · simpa [d, hi] using east_adj v
    · simpa [d, hi] using north_adj v
  obtain ⟨p, hp⟩ := horizontal_walk 0 x.1
  obtain ⟨q, hq⟩ := vertical_walk (0 + (x.1, 0)) x.2
  have hfinish : (0 : Lattice) + (x.1, 0) + (0, x.2) = x := by
    ext <;> simp
  let q' : nearestNeighborGraph.Walk (0 + (x.1, 0)) x := q.copy rfl hfinish
  obtain ⟨r, hr, hseg⟩ := unit_ray x d hd m
  let w := (p.append q').append r
  let S : Finset Lattice := w.support.toFinset
  have hconn : IsConnectedAnimal S := by
    have he : (↑S : Set Lattice) = {v | v ∈ w.support} := by
      ext z
      simp [S]
    rw [IsConnectedAnimal, he]
    exact w.connected_induce_support
  have hzero : (0 : Lattice) ∈ S := by
    simp [S]
  have hcard : S.card ≤ N := by
    calc
      S.card ≤ w.support.length := List.toFinset_card_le _
      _ = w.length + 1 := w.length_support
      _ = x.1.natAbs + x.2.natAbs + m + 1 := by simp [w, q', hp, hq, hr]
      _ ≤ N := hN
  obtain ⟨A, hA, hsub⟩ := hconn.exists_extension_mem_animalFamily hzero N hcard
  refine ⟨A, hA, ?_⟩
  intro k hk
  apply hsub
  change x + (k : ℤ) • d ∈ w.support.toFinset
  apply List.mem_toFinset.mpr
  exact (SimpleGraph.Walk.mem_support_append_iff (p.append q') r).2 (Or.inr (hseg k hk))

end LPPDifferentiability
