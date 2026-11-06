/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Algebra.BigOperators.Fin
import Lean.Elab.Tactic.Omega

/-! Exact-total selection below a vector of natural-number capacities. -/

@[expose] public section

open scoped BigOperators

namespace LPPDifferentiability

/-- Capacities with total at least `t` contain a vector bounded coordinatewise
by those capacities and with total exactly `t`. The proof fills coordinates in
order, taking the smaller of the current capacity and the remaining amount. -/
theorem exists_witness_allocation_below_of_le_sum {N t : ℕ}
    (capacity : Fin (N + 1) → ℕ)
    (ht : t ≤ ∑ i : Fin (N + 1), capacity i) :
    ∃ multiplicity : Fin (N + 1) → ℕ,
      (∀ i, multiplicity i ≤ capacity i) ∧
        (∑ i : Fin (N + 1), multiplicity i) = t := by
  revert t capacity
  induction N with
  | zero =>
      intro t capacity ht
      have hsum : (∑ i : Fin 1, capacity i) = capacity 0 :=
        Fin.sum_univ_one _
      have hcapacity : t ≤ capacity 0 := by
        change t ≤ (∑ i : Fin 1, capacity i) at ht
        rw [hsum] at ht
        exact ht
      refine ⟨fun _ => t, ?_, ?_⟩
      · intro i
        have hi : i = (0 : Fin 1) := by
          apply Fin.ext
          omega
        simpa only [hi] using hcapacity
      · simp
  | succ N ih =>
      intro t capacity ht
      have htotal : t ≤ capacity 0 + ∑ i : Fin (N + 1), capacity i.succ := by
        simpa only [Fin.sum_univ_succ] using ht
      have hremaining :
          t - min (capacity 0) t ≤ ∑ i : Fin (N + 1), capacity i.succ := by
        by_cases h : t ≤ capacity 0
        · rw [min_eq_right h]
          omega
        · have hlt : capacity 0 < t := by omega
          rw [min_eq_left hlt.le]
          omega
      obtain ⟨tail, htail, htail_sum⟩ :=
        ih (t := t - min (capacity 0) t)
          (fun i : Fin (N + 1) => capacity i.succ) hremaining
      refine ⟨Fin.cons (min (capacity 0) t) tail, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp only [Fin.cons_zero]
          exact min_le_left _ _
        · simp only [Fin.cons_succ]
          exact htail j
      · rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        rw [htail_sum]
        exact Nat.add_sub_of_le (min_le_right _ _)

end LPPDifferentiability
