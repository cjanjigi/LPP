/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.SquareBoundaryEdges
public import LPP_Foundations.Model.LatticeRayCrossingBalance
import Mathlib.Tactic

/-! Left-square incidence and a literal discrete crossing certificate.
No equality with analytic winding number is asserted here. -/

public section

namespace LPPDifferentiability

section Boundary

variable {S : Finset (Int × Int)} {E : Finset ((Int × Int) × (Int × Int))}
    (hmem : ∀ e, e ∈ E ↔ ∃ w, w ∈ S ∧
      ((e = ((w.1, w.2), (w.1 + 1, w.2)) ∧ (w.1, w.2 - 1) ∉ S) ∨
       (e = ((w.1 + 1, w.2), (w.1 + 1, w.2 + 1)) ∧ (w.1 + 1, w.2) ∉ S) ∨
       (e = ((w.1 + 1, w.2 + 1), (w.1, w.2 + 1)) ∧ (w.1, w.2 + 1) ∉ S) ∨
       (e = ((w.1, w.2 + 1), (w.1, w.2)) ∧ (w.1 - 1, w.2) ∉ S)))

include hmem

/-- The actual square rule supplies a left cell and its forward exit. -/
theorem square_boundary_edge_left_cell (e : Lattice × Lattice) (he : e ∈ E) :
    ∃ w ∈ S,
      (e.2 - e.1 = (0, 1) →
        e.1 = (w.1 + 1, w.2) ∧ e.2 = (w.1 + 1, w.2 + 1) ∧
        (w.1 + 1, w.2) ∉ S) ∧
      (e.2 - e.1 = (-1, 0) →
        e.1 = (w.1 + 1, w.2 + 1) ∧ e.2 = (w.1, w.2 + 1) ∧
        (w.1, w.2 + 1) ∉ S) := by
  obtain ⟨w, hw, hs⟩ := (hmem e).mp he
  refine ⟨w, hw, ?_, ?_⟩
  · intro hu
    rcases hs with ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn⟩
    · have hx := congrArg Prod.fst hu
      simp at hx
    · exact ⟨rfl, rfl, hn⟩
    · have hx := congrArg Prod.fst hu
      simp at hx
    · have hy := congrArg Prod.snd hu
      simp at hy
  · intro hl
    rcases hs with ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn⟩
    · have hx := congrArg Prod.fst hl
      simp at hx
    · have hx := congrArg Prod.fst hl
      simp at hx
    · exact ⟨rfl, rfl, hn⟩
    · have hx := congrArg Prod.fst hl
      simp at hx

/-- At x zero the only boundary crossing of y=1/2 is the origin's downward side. -/
theorem square_boundary_zero_line_crossing
    (hquadrant : ∀ w ∈ S, 0 ≤ w.1 ∧ 0 ≤ w.2)
    (e : Lattice × Lattice) (he : e ∈ E) (hx : e.1.1 = 0)
    (hy : (e.1.2 = 0 ∧ e.2.2 = 1) ∨ (e.1.2 = 1 ∧ e.2.2 = 0)) :
    e = ((0, 1), (0, 0)) := by
  obtain ⟨w, hw, hs⟩ := (hmem e).mp he
  obtain ⟨hwx, _⟩ := hquadrant w hw
  rcases hs with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
  · simp only at hy
    omega
  · simp only at hx
    omega
  · simp only at hy
    omega
  · simp only at hx hy
    have hwy : w.2 = 0 := by omega
    simp only [hx, hwy, zero_add]

/-- Select any edge-simple closed circuit containing the distinguished side.
Its literal positive horizontal-ray index is one. -/
theorem square_boundary_circuit_ray_sum_eq_one
    (hquadrant : ∀ w ∈ S, 0 ≤ w.1 ∧ 0 ≤ w.2)
    (m : ℕ) (v : Fin (m + 1) → Lattice)
    (hclosed : v 0 = v (Fin.last m))
    (hstep : ∀ i : Fin m,
      v i.succ - v i.castSucc = (0, 1) ∨
      v i.succ - v i.castSucc = (0, -1) ∨
      v i.succ - v i.castSucc = (-1, 0) ∨
      v i.succ - v i.castSucc = (1, 0))
    (hinj : Function.Injective (fun i : Fin m => (v i.castSucc, v i.succ)))
    (he : ∀ i : Fin m, (v i.castSucc, v i.succ) ∈ E)
    (k : Fin m) (hk : (v k.castSucc, v k.succ) = ((0, 1), (0, 0))) :
    (∑ i : Fin m,
      if (v i.castSucc).2 = 0 ∧ (v i.succ).2 = 1 ∧ 1 ≤ (v i.castSucc).1
      then (1 : ℤ)
      else if (v i.castSucc).2 = 1 ∧ (v i.succ).2 = 0 ∧ 1 ≤ (v i.castSucc).1
      then -1 else 0) = 1 := by
  classical
  have hdiff (i : Fin m) :
      (if (v i.castSucc).2 = 0 ∧ (v i.succ).2 = 1 then (1 : ℤ)
      else if (v i.castSucc).2 = 1 ∧ (v i.succ).2 = 0 then -1 else 0) =
      (if (v i.castSucc).2 = 0 ∧ (v i.succ).2 = 1 ∧ 1 ≤ (v i.castSucc).1
      then (1 : ℤ)
      else if (v i.castSucc).2 = 1 ∧ (v i.succ).2 = 0 ∧ 1 ≤ (v i.castSucc).1
      then -1 else 0) + (if i = k then -1 else 0) := by
    by_cases hik : i = k
    · subst i
      obtain ⟨ha, hb⟩ := Prod.mk.inj hk
      rw [ha, hb]
      norm_num
    · have hnot : (v i.castSucc, v i.succ) ≠ ((0, 1), (0, 0)) := by
        intro hh
        exact hik (hinj (hh.trans hk.symm))
      have hnonneg := (square_boundary_edges_stay_in_nonnegative_quadrant
        hmem hquadrant _ (he i)).1
      change 0 ≤ (v i.castSucc).1 at hnonneg
      have hzero : ¬ ((v i.castSucc).1 = 0 ∧
          ((v i.castSucc).2 = 0 ∧ (v i.succ).2 = 1 ∨
           (v i.castSucc).2 = 1 ∧ (v i.succ).2 = 0)) := by
        rintro ⟨hx, hy⟩
        exact hnot (square_boundary_zero_line_crossing hmem hquadrant _ (he i) hx hy)
      split_ifs <;> omega
  have hline := closed_lattice_walk_line_crossing_sum_eq_zero m v hclosed hstep
  simp_rw [hdiff] at hline
  rw [Finset.sum_add_distrib] at hline
  have hsingle : (∑ i : Fin m, if i = k then (-1 : ℤ) else 0) = -1 := by
    simp
  rw [hsingle] at hline
  omega

end Boundary

end LPPDifferentiability
