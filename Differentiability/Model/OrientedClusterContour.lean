/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.FiniteOrientedCluster
public import Differentiability.Model.OrientedBoundaryCircuit

/-! The actual finite endpoint set supplies its actual boundary circuit. -/

public section

namespace LPPDifferentiability

/-- No infinite all-good path gives the actual finite endpoint set and its
boundary circuit, with the endpoint membership condition unchanged. -/
theorem exists_finite_oriented_cluster_boundary_circuit
    (G : Set (ℕ × ℕ))
    (hno : ¬ ∃ v : ℕ → ℕ × ℕ, v 0 = (0, 0) ∧
      (∀ i, v (i + 1) = v i + (1, 0) ∨ v (i + 1) = v i + (0, 1)) ∧
      ∀ i, v i ∈ G) :
    ∃ S : Finset (ℕ × ℕ),
      ∃ _hS : (∀ x, x ∈ S ↔ x ∈ {y : ℕ × ℕ | ∃ n : ℕ,
        ∃ q : Fin (n + 1) → ℕ × ℕ,
          q 0 = (0, 0) ∧ q (Fin.last n) = y ∧
          (∀ i : Fin n,
            q i.succ = q i.castSucc + (1, 0) ∨
            q i.succ = q i.castSucc + (0, 1)) ∧
          ∀ i : Fin (n + 1), (i : ℕ) < n → q i ∈ G}),
      let T : Finset Lattice :=
        S.image (fun x => ((x.1 : ℤ), (x.2 : ℤ)))
      ∃ (E : Finset (Lattice × Lattice)) (m : ℕ)
        (v : Fin (m + 1) → Lattice) (w : Fin m → ℕ × ℕ),
        (∀ e, e ∈ E ↔ ∃ z, z ∈ T ∧
          ((e = ((z.1, z.2), (z.1 + 1, z.2)) ∧ (z.1, z.2 - 1) ∉ T) ∨
           (e = ((z.1 + 1, z.2), (z.1 + 1, z.2 + 1)) ∧
            (z.1 + 1, z.2) ∉ T) ∨
           (e = ((z.1 + 1, z.2 + 1), (z.1, z.2 + 1)) ∧
            (z.1, z.2 + 1) ∉ T) ∨
           (e = ((z.1, z.2 + 1), (z.1, z.2)) ∧ (z.1 - 1, z.2) ∉ T))) ∧
        4 ≤ m ∧
        v 0 = v (Fin.last m) ∧
        Function.Injective (fun i : Fin m => (v i.castSucc, v i.succ)) ∧
        (∀ i : Fin m, (v i.castSucc, v i.succ) ∈ E) ∧
        (∀ i : Fin m,
          v i.succ - v i.castSucc = (0, 1) ∨
          v i.succ - v i.castSucc = (0, -1) ∨
          v i.succ - v i.castSucc = (-1, 0) ∨
          v i.succ - v i.castSucc = (1, 0)) ∧
        (∑ i : Fin m,
          if (v i.castSucc).2 = 0 ∧ (v i.succ).2 = 1 ∧
            1 ≤ (v i.castSucc).1 then (1 : ℤ)
          else if (v i.castSucc).2 = 1 ∧ (v i.succ).2 = 0 ∧
            1 ≤ (v i.castSucc).1 then -1 else 0) = 1 ∧
        (∀ i j : Fin m,
          (v i.succ, v i.castSucc) ≠ (v j.castSucc, v j.succ)) ∧
        (∀ i, 0 ≤ (v i).1 ∧ (v i).1 ≤ (m : ℤ) + 1 ∧
          0 ≤ (v i).2 ∧ (v i).2 ≤ (m : ℤ) + 1) ∧
        (∀ i : Fin m, w i ∈ S ∧
          (v i.succ - v i.castSucc = (0, 1) →
            v i.castSucc = (((w i).1 : ℤ) + 1, ((w i).2 : ℤ)) ∧
            v i.succ = (((w i).1 : ℤ) + 1, ((w i).2 : ℤ) + 1) ∧
            w i + (1, 0) ∉ S) ∧
          (v i.succ - v i.castSucc = (-1, 0) →
            v i.castSucc = (((w i).1 : ℤ) + 1, ((w i).2 : ℤ) + 1) ∧
            v i.succ = (((w i).1 : ℤ), ((w i).2 : ℤ) + 1) ∧
            w i + (0, 1) ∉ S)) ∧
        (let A : Finset (Fin m) :=
          (Finset.univ.filter (fun i =>
            v i.succ - v i.castSucc = (0, 1))) ∪
          (Finset.univ.filter (fun i =>
            v i.succ - v i.castSucc = (-1, 0)))
         (∀ x ∈ A.image w, x ∉ G) ∧ m ≤ 8 * (A.image w).card) := by
  classical
  have hfinite := finite_oriented_endpoint_set G hno
  let S : Finset (ℕ × ℕ) := hfinite.toFinset
  have hS : ∀ x, x ∈ S ↔ x ∈ {y : ℕ × ℕ | ∃ n : ℕ,
      ∃ q : Fin (n + 1) → ℕ × ℕ,
        q 0 = (0, 0) ∧ q (Fin.last n) = y ∧
        (∀ i : Fin n,
          q i.succ = q i.castSucc + (1, 0) ∨
          q i.succ = q i.castSucc + (0, 1)) ∧
        ∀ i : Fin (n + 1), (i : ℕ) < n → q i ∈ G} := by
    intro x
    exact hfinite.mem_toFinset
  exact ⟨S, hS, exists_oriented_endpoint_boundary_circuit G S hS⟩

end LPPDifferentiability
