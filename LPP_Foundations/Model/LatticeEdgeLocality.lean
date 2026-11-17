/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.LatticeEdgeIntegration

/-!
# Locality of lattice edge path sums

For ordered endpoints, the literal horizontal-then-vertical path stays in the
future cone rooted at its starting point. Therefore its value depends only on
the edge field in that cone.
-/

@[expose] public section

open scoped BigOperators

namespace LPPDifferentiability

/-- The literal coordinate path sum is determined by the edge field on the
future cone of its starting point. This is the deterministic locality step for
the path construction in JR1810.03580v3, proof of Theorem 4.8 after (4.19). -/
theorem lattice_edge_coordinate_path_sum_eq_of_agree_on_future_cone
    (E F : Lattice → Fin 2 → ℝ) (x y : Lattice) (hxy : x ≤ y)
    (hEq : ∀ u ∈ Set.Ici x, ∀ i, E u i = F u i) :
    let S : (ℤ → ℝ) → ℤ → ℤ → ℝ := fun f a b =>
      if a ≤ b then ∑ k ∈ Finset.Ico a b, f k
      else -(∑ k ∈ Finset.Ico b a, f k)
    let R : (Lattice → Fin 2 → ℝ) → Lattice → Lattice → ℝ := fun G a b =>
      S (fun k => G (k, a.2) 0) a.1 b.1 +
        S (fun k => G (b.1, k) 1) a.2 b.2
    R E x y = R F x y := by
  dsimp only
  have hx1 : x.1 ≤ y.1 := hxy.1
  have hx2 : x.2 ≤ y.2 := hxy.2
  simp only [ite_eq_left hx1, ite_eq_left hx2]
  have hHorizontal :
      (∑ k ∈ Finset.Ico x.1 y.1, E (k, x.2) 0) =
        ∑ k ∈ Finset.Ico x.1 y.1, F (k, x.2) 0 := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkLower : x.1 ≤ k := (Finset.mem_Ico.mp hk).1
    have hSite : (k, x.2) ∈ Set.Ici x := by
      change x ≤ (k, x.2)
      exact ⟨hkLower, le_rfl⟩
    exact hEq (k, x.2) hSite 0
  have hVertical :
      (∑ k ∈ Finset.Ico x.2 y.2, E (y.1, k) 1) =
        ∑ k ∈ Finset.Ico x.2 y.2, F (y.1, k) 1 := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkLower : x.2 ≤ k := (Finset.mem_Ico.mp hk).1
    have hSite : (y.1, k) ∈ Set.Ici x := by
      change x ≤ (y.1, k)
      exact ⟨hx1, hkLower⟩
    exact hEq (y.1, k) hSite 1
  rw [hHorizontal, hVertical]

end LPPDifferentiability
