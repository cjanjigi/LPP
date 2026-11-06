/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.SquareBoundaryCrossings
public import Differentiability.Model.SquareBoundaryBalance
public import Differentiability.Model.FiniteDirectedCircuitDecomposition
public import LPP_Foundations.Model.LatticeRayCrossingBounds
import Mathlib.Tactic

/-! An actual circuit in the uncancelled boundary of a finite square family.
The index is the literal discrete ray sum, with no analytic winding claim. -/

public section

namespace LPPDifferentiability

/-- The same actual square boundary and Euler circuit provide the nonzero ray
index, unit geometry, forward-side incidences and the translated vertex box. -/
theorem exists_square_boundary_circuit (S : Finset Lattice)
    (hquadrant : ∀ w ∈ S, 0 ≤ w.1 ∧ 0 ≤ w.2) (hzero : (0, 0) ∈ S) :
    ∃ (E : Finset (Lattice × Lattice)) (m : ℕ)
      (v : Fin (m + 1) → Lattice) (w : Fin m → Lattice),
      (∀ e, e ∈ E ↔ ∃ z, z ∈ S ∧
        ((e = ((z.1, z.2), (z.1 + 1, z.2)) ∧ (z.1, z.2 - 1) ∉ S) ∨
         (e = ((z.1 + 1, z.2), (z.1 + 1, z.2 + 1)) ∧ (z.1 + 1, z.2) ∉ S) ∨
         (e = ((z.1 + 1, z.2 + 1), (z.1, z.2 + 1)) ∧ (z.1, z.2 + 1) ∉ S) ∨
         (e = ((z.1, z.2 + 1), (z.1, z.2)) ∧ (z.1 - 1, z.2) ∉ S))) ∧
      4 ≤ m ∧ v 0 = v (Fin.last m) ∧
      Function.Injective (fun i : Fin m => (v i.castSucc, v i.succ)) ∧
      (∀ i : Fin m, (v i.castSucc, v i.succ) ∈ E) ∧
      (∀ i : Fin m,
        v i.succ - v i.castSucc = (0, 1) ∨
        v i.succ - v i.castSucc = (0, -1) ∨
        v i.succ - v i.castSucc = (-1, 0) ∨
        v i.succ - v i.castSucc = (1, 0)) ∧
      (∃ k : Fin m, (v k.castSucc, v k.succ) = ((0, 1), (0, 0))) ∧
      (∑ i : Fin m,
        if (v i.castSucc).2 = 0 ∧ (v i.succ).2 = 1 ∧ 1 ≤ (v i.castSucc).1
        then (1 : ℤ)
        else if (v i.castSucc).2 = 1 ∧ (v i.succ).2 = 0 ∧ 1 ≤ (v i.castSucc).1
        then -1 else 0) = 1 ∧
      (∀ i j : Fin m, (v i.succ, v i.castSucc) ≠ (v j.castSucc, v j.succ)) ∧
      (∀ i, 0 ≤ (v i).1 ∧ (v i).1 ≤ (m : ℤ) + 1 ∧
        0 ≤ (v i).2 ∧ (v i).2 ≤ (m : ℤ) + 1) ∧
      (∀ i : Fin m, w i ∈ S ∧
        (v i.succ - v i.castSucc = (0, 1) →
          v i.castSucc = ((w i).1 + 1, (w i).2) ∧
          v i.succ = ((w i).1 + 1, (w i).2 + 1) ∧ ((w i).1 + 1, (w i).2) ∉ S) ∧
        (v i.succ - v i.castSucc = (-1, 0) →
          v i.castSucc = ((w i).1 + 1, (w i).2 + 1) ∧
          v i.succ = ((w i).1, (w i).2 + 1) ∧ ((w i).1, (w i).2 + 1) ∉ S)) := by
  classical
  obtain ⟨E, hmem, hbalance, hunit, hreverse, hquad, hleft⟩ :=
    exists_balanced_square_boundary S
  obtain ⟨n, lengths, vertices, hcircuits, _, hcover⟩ :=
    finite_directed_circuit_decomposition E (fun x => (hbalance x).symm)
  have hdist := hleft hquadrant hzero
  rw [← hcover] at hdist
  obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hdist
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hj
  let m := lengths j
  let v : Fin (m + 1) → Lattice := vertices j
  obtain ⟨hm, hclosed, hinj⟩ := hcircuits j
  have he (i : Fin m) : (v i.castSucc, v i.succ) ∈ E := by
    rw [← hcover]
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _,
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  have hstep (i : Fin m) :
      v i.succ - v i.castSucc = (0, 1) ∨
      v i.succ - v i.castSucc = (0, -1) ∨
      v i.succ - v i.castSucc = (-1, 0) ∨
      v i.succ - v i.castSucc = (1, 0) := by
    have hu := hunit _ (he i)
    simp only at hu
    rcases hu with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
    · right; right; right
      apply Prod.ext <;> simp only [Prod.fst_sub, Prod.snd_sub] <;> omega
    · left
      apply Prod.ext <;> simp only [Prod.fst_sub, Prod.snd_sub] <;> omega
    · right; right; left
      apply Prod.ext <;> simp only [Prod.fst_sub, Prod.snd_sub] <;> omega
    · right; left
      apply Prod.ext <;> simp only [Prod.fst_sub, Prod.snd_sub] <;> omega
  have hnonneg : ∀ i, 0 ≤ (v i).1 ∧ 0 ≤ (v i).2 := by
    intro i
    induction i using Fin.cases with
    | zero => exact ⟨(hquad hquadrant _ (he ⟨0, hm⟩)).1,
        (hquad hquadrant _ (he ⟨0, hm⟩)).2.1⟩
    | succ i => exact ⟨(hquad hquadrant _ (he i)).2.2.1,
        (hquad hquadrant _ (he i)).2.2.2⟩
  have hindex := square_boundary_circuit_ray_sum_eq_one hmem hquadrant
    m v hclosed hstep hinj he k hk
  have hindex_ne : (∑ i : Fin m,
      if (v i.castSucc).2 = 0 ∧ (v i.succ).2 = 1 ∧ 1 ≤ (v i.castSucc).1
      then (1 : ℤ)
      else if (v i.castSucc).2 = 1 ∧ (v i.succ).2 = 0 ∧ 1 ≤ (v i.castSucc).1
      then -1 else 0) ≠ 0 := by omega
  have hcells (i : Fin m) := square_boundary_edge_left_cell hmem _ (he i)
  choose w hw hinc using hcells
  refine ⟨E, m, v, w, hmem,
    four_le_length_of_ray_sum_ne_zero m v hclosed hstep hindex_ne,
    hclosed, hinj, he, hstep, ⟨k, hk⟩, hindex, ?_,
    lattice_walk_vertex_bounds_of_ray_sum_ne_zero m v hclosed hstep hnonneg hindex_ne, ?_⟩
  · intro i j hij
    exact hreverse _ (he i) (hij ▸ he j)
  · intro i
    exact ⟨hw i, (hinc i).1, (hinc i).2⟩

end LPPDifferentiability
