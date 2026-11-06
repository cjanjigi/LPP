/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.ClosedLatticeWalkCounts
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega

/-! Literal horizontal-line crossing balance for actual closed unit lattice walks.
This does not identify the discrete sum with analytic winding number. -/

@[expose] public section

namespace LPPDifferentiability

private theorem unit_step_coordinate_facts (a b : Lattice)
    (h : b - a = (0, 1) ∨ b - a = (0, -1) ∨
      b - a = (-1, 0) ∨ b - a = (1, 0)) :
    (-1 ≤ b.1 - a.1 ∧ b.1 - a.1 ≤ 1) ∧
    (-1 ≤ b.2 - a.2 ∧ b.2 - a.2 ≤ 1) ∧
    (a.2 ≠ b.2 → a.1 = b.1) := by
  rcases h with h | h | h | h <;>
    have hx := congrArg Prod.fst h <;>
    have hy := congrArg Prod.snd h <;>
    simp only [Prod.fst_sub, Prod.snd_sub] at hx hy <;> omega

/-- The signed crossings of the entire horizontal line cancel on a closed walk. -/
theorem closed_lattice_walk_line_crossing_sum_eq_zero
    (m : ℕ) (v : Fin (m + 1) → Lattice)
    (hclosed : v 0 = v (Fin.last m))
    (hstep : ∀ i : Fin m,
      v i.succ - v i.castSucc = (0, 1) ∨
      v i.succ - v i.castSucc = (0, -1) ∨
      v i.succ - v i.castSucc = (-1, 0) ∨
      v i.succ - v i.castSucc = (1, 0)) :
    (∑ i : Fin m,
      if (v i.castSucc).2 = 0 ∧ (v i.succ).2 = 1 then (1 : ℤ)
      else if (v i.castSucc).2 = 1 ∧ (v i.succ).2 = 0 then -1 else 0) = 0 := by
  classical
  have hedge (i : Fin m) :
      (if (v i.castSucc).2 = 0 ∧ (v i.succ).2 = 1 then (1 : ℤ)
      else if (v i.castSucc).2 = 1 ∧ (v i.succ).2 = 0 then -1 else 0) =
      (if 1 ≤ (v i.succ).2 then (1 : ℤ) else 0) -
      (if 1 ≤ (v i.castSucc).2 then (1 : ℤ) else 0) := by
    have hy := (unit_step_coordinate_facts _ _ (hstep i)).2.1
    split_ifs <;> omega
  simp_rw [hedge]
  rw [Finset.sum_sub_distrib]
  have hsum := Fin.sum_univ_succ
    (fun i : Fin (m + 1) => if 1 ≤ (v i).2 then (1 : ℤ) else 0)
  have hsum' := Fin.sum_univ_castSucc
    (fun i : Fin (m + 1) => if 1 ≤ (v i).2 then (1 : ℤ) else 0)
  rw [← hclosed] at hsum'
  omega

/-- A nonzero literal positive-ray sum forces an actual crossing at x zero. -/
theorem exists_zero_x_crossing_of_ray_sum_ne_zero
    (m : ℕ) (v : Fin (m + 1) → Lattice)
    (hclosed : v 0 = v (Fin.last m))
    (hstep : ∀ i : Fin m,
      v i.succ - v i.castSucc = (0, 1) ∨
      v i.succ - v i.castSucc = (0, -1) ∨
      v i.succ - v i.castSucc = (-1, 0) ∨
      v i.succ - v i.castSucc = (1, 0))
    (hnonneg : ∀ i, 0 ≤ (v i).1 ∧ 0 ≤ (v i).2)
    (hindex : (∑ i : Fin m,
      if (v i.castSucc).2 = 0 ∧ (v i.succ).2 = 1 ∧ 1 ≤ (v i.castSucc).1
      then (1 : ℤ)
      else if (v i.castSucc).2 = 1 ∧ (v i.succ).2 = 0 ∧ 1 ≤ (v i.castSucc).1
      then -1 else 0) ≠ 0) :
    ∃ i : Fin m, (v i.castSucc).1 = 0 ∧
      ((v i.castSucc).2 = 0 ∧ (v i.succ).2 = 1 ∨
       (v i.castSucc).2 = 1 ∧ (v i.succ).2 = 0) := by
  classical
  by_contra hnone
  apply hindex
  apply Eq.trans (b := ∑ i : Fin m,
    if (v i.castSucc).2 = 0 ∧ (v i.succ).2 = 1 then (1 : ℤ)
    else if (v i.castSucc).2 = 1 ∧ (v i.succ).2 = 0 then -1 else 0)
  swap
  · exact closed_lattice_walk_line_crossing_sum_eq_zero m v hclosed hstep
  apply Finset.sum_congr rfl
  intro i _
  have hnon := (hnonneg i.castSucc).1
  have hno : ¬ ((v i.castSucc).1 = 0 ∧
      ((v i.castSucc).2 = 0 ∧ (v i.succ).2 = 1 ∨
       (v i.castSucc).2 = 1 ∧ (v i.succ).2 = 0)) := by
    intro h
    exact hnone ⟨i, h⟩
  split_ifs <;> omega

/-- The x-zero crossing has the actual origin as one of its endpoints. -/
theorem exists_origin_vertex_of_ray_sum_ne_zero
    (m : ℕ) (v : Fin (m + 1) → Lattice)
    (hclosed : v 0 = v (Fin.last m))
    (hstep : ∀ i : Fin m,
      v i.succ - v i.castSucc = (0, 1) ∨
      v i.succ - v i.castSucc = (0, -1) ∨
      v i.succ - v i.castSucc = (-1, 0) ∨
      v i.succ - v i.castSucc = (1, 0))
    (hnonneg : ∀ i, 0 ≤ (v i).1 ∧ 0 ≤ (v i).2)
    (hindex : (∑ i : Fin m,
      if (v i.castSucc).2 = 0 ∧ (v i.succ).2 = 1 ∧ 1 ≤ (v i.castSucc).1
      then (1 : ℤ)
      else if (v i.castSucc).2 = 1 ∧ (v i.succ).2 = 0 ∧ 1 ≤ (v i.castSucc).1
      then -1 else 0) ≠ 0) :
    ∃ j : Fin (m + 1), v j = (0, 0) := by
  obtain ⟨i, hx, hcross⟩ :=
    exists_zero_x_crossing_of_ray_sum_ne_zero m v hclosed hstep hnonneg hindex
  rcases hcross with ⟨hy, _⟩ | ⟨hy, hy'⟩
  · exact ⟨i.castSucc, Prod.ext hx hy⟩
  · have hx' := (unit_step_coordinate_facts _ _ (hstep i)).2.2 (by omega)
    exact ⟨i.succ, Prod.ext (by omega) hy'⟩

end LPPDifferentiability
