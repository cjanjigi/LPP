/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.FiniteNonbacktrackingWalks
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Finset.Prod
import Lean.Elab.Tactic.Omega

/-! The square-box factor in the contour count.
Only the enumeration of walks is proved here; choosing a contour is a separate step. -/
public section

namespace LPPDifferentiability

/-- The integer start box has exactly `(m+2)^2` points. -/
theorem card_lattice_start_box (m : ℕ) :
    ((Finset.Icc (0 : ℤ) (m + 1)).product
      (Finset.Icc (0 : ℤ) (m + 1))).card = (m + 2) ^ 2 := by
  rw [Finset.product_eq_sprod, Finset.card_product, Int.card_Icc]
  have h : ((m : ℤ) + 1 + 1 - 0).toNat = m + 2 := by omega
  rw [h]
  exact (pow_two (m + 2)).symm

/-- The nonbacktracking walks starting in `[0,m+1]^2` form a finite set, with the
exact upper bound stated here. This includes open walks; circuits can use the bound
after a separate subset and location argument. The positive-length domain includes
`m ≥ 4`. -/
theorem exists_finset_nonbacktracking_walks_in_box (m : ℕ) (hm : 0 < m) :
    ∃ W : Finset (Fin (m + 1) → Lattice),
      (∀ v, v ∈ W ↔
        (0 ≤ (v 0).1 ∧ (v 0).1 ≤ (m : ℤ) + 1) ∧
        (0 ≤ (v 0).2 ∧ (v 0).2 ≤ (m : ℤ) + 1) ∧
        (∀ i : Fin m, v i.succ - v i.castSucc = (0, 1) ∨
          v i.succ - v i.castSucc = (0, -1) ∨
          v i.succ - v i.castSucc = (-1, 0) ∨
          v i.succ - v i.castSucc = (1, 0)) ∧
        (∀ (i : ℕ) (hi : i + 2 ≤ m),
          v ⟨i + 2, by omega⟩ ≠ v ⟨i, by omega⟩)) ∧
      W.card ≤ (m + 2) ^ 2 * 4 * 3 ^ (m - 1) := by
  obtain ⟨W, hW, hcard⟩ := exists_finset_nonbacktracking_walks_from
    ((Finset.Icc (0 : ℤ) (m + 1)).product (Finset.Icc (0 : ℤ) (m + 1))) m hm
  refine ⟨W, ?_, ?_⟩
  · intro v
    rw [hW, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    exact and_assoc
  · rw [card_lattice_start_box] at hcard
    exact hcard

end LPPDifferentiability
