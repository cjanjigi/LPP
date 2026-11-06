/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.SquareBoundaryEdges
public import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! Actual degree balance after cancelling shared square sides. -/

public section

namespace LPPDifferentiability

private theorem square_boundary_mem_right
    {S : Finset (Int × Int)} {E : Finset ((Int × Int) × (Int × Int))}
    (hmem : ∀ e, e ∈ E ↔ ∃ w, w ∈ S ∧
      ((e = ((w.1, w.2), (w.1 + 1, w.2)) ∧ (w.1, w.2 - 1) ∉ S) ∨
       (e = ((w.1 + 1, w.2), (w.1 + 1, w.2 + 1)) ∧ (w.1 + 1, w.2) ∉ S) ∨
       (e = ((w.1 + 1, w.2 + 1), (w.1, w.2 + 1)) ∧ (w.1, w.2 + 1) ∉ S) ∨
       (e = ((w.1, w.2 + 1), (w.1, w.2)) ∧ (w.1 - 1, w.2) ∉ S)))
    (x y : Int) : ((x, y), (x + 1, y)) ∈ E ↔ (x, y) ∈ S ∧ (x, y - 1) ∉ S := by
  rw [hmem]
  constructor
  · rintro ⟨⟨a, b⟩, hw, hside⟩
    rcases hside with ⟨he, hn⟩ | ⟨he, hn⟩ | ⟨he, hn⟩ | ⟨he, hn⟩
    · simp only [Prod.mk.injEq] at he
      obtain ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩ := he
      have ha : a = x := by omega
      have hb : b = y := by omega
      subst a b
      simpa using And.intro hw hn
    · simp only [Prod.mk.injEq] at he
      omega
    · simp only [Prod.mk.injEq] at he
      omega
    · simp only [Prod.mk.injEq] at he
      omega
  · rintro ⟨hw, hn⟩
    refine ⟨(x, y), hw, ?_⟩
    left
    constructor
    · simp
    · simpa using hn

private theorem square_boundary_mem_up
    {S : Finset (Int × Int)} {E : Finset ((Int × Int) × (Int × Int))}
    (hmem : ∀ e, e ∈ E ↔ ∃ w, w ∈ S ∧
      ((e = ((w.1, w.2), (w.1 + 1, w.2)) ∧ (w.1, w.2 - 1) ∉ S) ∨
       (e = ((w.1 + 1, w.2), (w.1 + 1, w.2 + 1)) ∧ (w.1 + 1, w.2) ∉ S) ∨
       (e = ((w.1 + 1, w.2 + 1), (w.1, w.2 + 1)) ∧ (w.1, w.2 + 1) ∉ S) ∨
       (e = ((w.1, w.2 + 1), (w.1, w.2)) ∧ (w.1 - 1, w.2) ∉ S)))
    (x y : Int) : ((x, y), (x, y + 1)) ∈ E ↔ (x - 1, y) ∈ S ∧ (x, y) ∉ S := by
  rw [hmem]
  constructor
  · rintro ⟨⟨a, b⟩, hw, hside⟩
    rcases hside with ⟨he, hn⟩ | ⟨he, hn⟩ | ⟨he, hn⟩ | ⟨he, hn⟩
    · simp only [Prod.mk.injEq] at he
      omega
    · simp only [Prod.mk.injEq] at he
      obtain ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩ := he
      have ha : a = x - 1 := by omega
      have hb : b = y := by omega
      subst a b
      simpa using And.intro hw hn
    · simp only [Prod.mk.injEq] at he
      omega
    · simp only [Prod.mk.injEq] at he
      omega
  · rintro ⟨hw, hn⟩
    refine ⟨(x - 1, y), hw, ?_⟩
    right; left
    constructor
    · simp
    · simpa using hn

private theorem square_boundary_mem_left
    {S : Finset (Int × Int)} {E : Finset ((Int × Int) × (Int × Int))}
    (hmem : ∀ e, e ∈ E ↔ ∃ w, w ∈ S ∧
      ((e = ((w.1, w.2), (w.1 + 1, w.2)) ∧ (w.1, w.2 - 1) ∉ S) ∨
       (e = ((w.1 + 1, w.2), (w.1 + 1, w.2 + 1)) ∧ (w.1 + 1, w.2) ∉ S) ∨
       (e = ((w.1 + 1, w.2 + 1), (w.1, w.2 + 1)) ∧ (w.1, w.2 + 1) ∉ S) ∨
       (e = ((w.1, w.2 + 1), (w.1, w.2)) ∧ (w.1 - 1, w.2) ∉ S)))
    (x y : Int) : ((x, y), (x - 1, y)) ∈ E ↔ (x - 1, y - 1) ∈ S ∧ (x - 1, y) ∉ S := by
  rw [hmem]
  constructor
  · rintro ⟨⟨a, b⟩, hw, hside⟩
    rcases hside with ⟨he, hn⟩ | ⟨he, hn⟩ | ⟨he, hn⟩ | ⟨he, hn⟩
    · simp only [Prod.mk.injEq] at he
      omega
    · simp only [Prod.mk.injEq] at he
      omega
    · simp only [Prod.mk.injEq] at he
      obtain ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩ := he
      have ha : a = x - 1 := by omega
      have hb : b = y - 1 := by omega
      subst a b
      simpa using And.intro hw hn
    · simp only [Prod.mk.injEq] at he
      omega
  · rintro ⟨hw, hn⟩
    refine ⟨(x - 1, y - 1), hw, ?_⟩
    right; right; left
    constructor
    · simp
    · simpa using hn

private theorem square_boundary_mem_down
    {S : Finset (Int × Int)} {E : Finset ((Int × Int) × (Int × Int))}
    (hmem : ∀ e, e ∈ E ↔ ∃ w, w ∈ S ∧
      ((e = ((w.1, w.2), (w.1 + 1, w.2)) ∧ (w.1, w.2 - 1) ∉ S) ∨
       (e = ((w.1 + 1, w.2), (w.1 + 1, w.2 + 1)) ∧ (w.1 + 1, w.2) ∉ S) ∨
       (e = ((w.1 + 1, w.2 + 1), (w.1, w.2 + 1)) ∧ (w.1, w.2 + 1) ∉ S) ∨
       (e = ((w.1, w.2 + 1), (w.1, w.2)) ∧ (w.1 - 1, w.2) ∉ S)))
    (x y : Int) : ((x, y), (x, y - 1)) ∈ E ↔ (x, y - 1) ∈ S ∧ (x - 1, y - 1) ∉ S := by
  rw [hmem]
  constructor
  · rintro ⟨⟨a, b⟩, hw, hside⟩
    rcases hside with ⟨he, hn⟩ | ⟨he, hn⟩ | ⟨he, hn⟩ | ⟨he, hn⟩
    · simp only [Prod.mk.injEq] at he
      omega
    · simp only [Prod.mk.injEq] at he
      omega
    · simp only [Prod.mk.injEq] at he
      omega
    · simp only [Prod.mk.injEq] at he
      obtain ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩ := he
      have ha : a = x := by omega
      have hb : b = y - 1 := by omega
      subst a b
      simpa using And.intro hw hn
  · rintro ⟨hw, hn⟩
    refine ⟨(x, y - 1), hw, ?_⟩
    right; right; right
    constructor
    · simp
    · simpa using hn

/-- The actual remaining boundary has equal incoming and outgoing degrees. -/
theorem square_boundary_edges_degree_balance
    {S : Finset (Int × Int)} {E : Finset ((Int × Int) × (Int × Int))}
    (hmem : ∀ e, e ∈ E ↔ ∃ w, w ∈ S ∧
      ((e = ((w.1, w.2), (w.1 + 1, w.2)) ∧ (w.1, w.2 - 1) ∉ S) ∨
       (e = ((w.1 + 1, w.2), (w.1 + 1, w.2 + 1)) ∧ (w.1 + 1, w.2) ∉ S) ∨
       (e = ((w.1 + 1, w.2 + 1), (w.1, w.2 + 1)) ∧ (w.1, w.2 + 1) ∉ S) ∨
       (e = ((w.1, w.2 + 1), (w.1, w.2)) ∧ (w.1 - 1, w.2) ∉ S))) :
    ∀ v : Int × Int, (E.filter (fun e => e.2 = v)).card =
      (E.filter (fun e => e.1 = v)).card := by
  classical
  rintro ⟨x, y⟩
  have hin : E.filter (fun e => e.2 = (x, y)) =
      ({((x - 1, y), (x, y)), ((x, y - 1), (x, y)),
        ((x + 1, y), (x, y)), ((x, y + 1), (x, y))} :
        Finset ((Int × Int) × (Int × Int))).filter (fun e => e ∈ E) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨he, hv⟩
      refine ⟨?_, he⟩
      have hu := square_boundary_edges_are_unit_steps hmem e he
      rcases e with ⟨⟨a,b⟩,⟨c,d⟩⟩
      simp only [Prod.mk.injEq] at hv ⊢
      rcases hu with h | h | h | h <;> simp only at h <;> omega
    · rintro ⟨he, hE⟩
      refine ⟨hE, ?_⟩
      rcases he with rfl | rfl | rfl | rfl <;> rfl
  have hout : E.filter (fun e => e.1 = (x, y)) =
      ({((x, y), (x + 1, y)), ((x, y), (x, y + 1)),
        ((x, y), (x - 1, y)), ((x, y), (x, y - 1))} :
        Finset ((Int × Int) × (Int × Int))).filter (fun e => e ∈ E) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨he, hv⟩
      refine ⟨?_, he⟩
      have hu := square_boundary_edges_are_unit_steps hmem e he
      rcases e with ⟨⟨a,b⟩,⟨c,d⟩⟩
      simp only [Prod.mk.injEq] at hv ⊢
      rcases hu with h | h | h | h <;> simp only at h <;> omega
    · rintro ⟨he, hE⟩
      refine ⟨hE, ?_⟩
      rcases he with rfl | rfl | rfl | rfl <;> rfl
  rw [hin, hout]
  have hr := square_boundary_mem_right hmem
  have hu := square_boundary_mem_up hmem
  have hl := square_boundary_mem_left hmem
  have hd := square_boundary_mem_down hmem
  have hi₁ : ((x - 1, y), (x, y)) ∈ E ↔ (x - 1, y) ∈ S ∧ (x - 1, y - 1) ∉ S := by
    simpa using hr (x - 1) y
  have hi₂ : ((x, y - 1), (x, y)) ∈ E ↔ (x - 1, y - 1) ∈ S ∧ (x, y - 1) ∉ S := by
    simpa using hu x (y - 1)
  have hi₃ : ((x + 1, y), (x, y)) ∈ E ↔ (x, y - 1) ∈ S ∧ (x, y) ∉ S := by
    simpa using hl (x + 1) y
  have hi₄ : ((x, y + 1), (x, y)) ∈ E ↔ (x, y) ∈ S ∧ (x - 1, y) ∉ S := by
    simpa using hd x (y + 1)
  have hx : x - 1 ≠ x + 1 := by omega
  have hy : y - 1 ≠ y + 1 := by omega
  by_cases h₁ : (x, y) ∈ S <;> by_cases h₂ : (x - 1, y) ∈ S <;>
    by_cases h₃ : (x - 1, y - 1) ∈ S <;> by_cases h₄ : (x, y - 1) ∈ S <;>
    simp [Finset.filter_insert, Finset.filter_singleton, hi₁, hi₂, hi₃, hi₄, hr, hu, hl, hd, h₁, h₂, h₃, h₄,
      Prod.mk.injEq, hx, hy, Ne.symm hx, Ne.symm hy]

/-- A finite square family produces one actual boundary satisfying geometry
and degree balance, including the conditional quadrant consequences. -/
theorem exists_balanced_square_boundary (S : Finset (Int × Int)) :
    ∃ E : Finset ((Int × Int) × (Int × Int)),
      (∀ e, e ∈ E ↔ ∃ w, w ∈ S ∧
        ((e = ((w.1, w.2), (w.1 + 1, w.2)) ∧ (w.1, w.2 - 1) ∉ S) ∨
         (e = ((w.1 + 1, w.2), (w.1 + 1, w.2 + 1)) ∧ (w.1 + 1, w.2) ∉ S) ∨
         (e = ((w.1 + 1, w.2 + 1), (w.1, w.2 + 1)) ∧ (w.1, w.2 + 1) ∉ S) ∨
         (e = ((w.1, w.2 + 1), (w.1, w.2)) ∧ (w.1 - 1, w.2) ∉ S))) ∧
      (∀ v, (E.filter (fun e => e.2 = v)).card =
        (E.filter (fun e => e.1 = v)).card) ∧
      (∀ e ∈ E,
        (e.2.1 = e.1.1 + 1 ∧ e.2.2 = e.1.2) ∨
        (e.2.1 = e.1.1 ∧ e.2.2 = e.1.2 + 1) ∨
        (e.2.1 = e.1.1 - 1 ∧ e.2.2 = e.1.2) ∨
        (e.2.1 = e.1.1 ∧ e.2.2 = e.1.2 - 1)) ∧
      (∀ e ∈ E, (e.2, e.1) ∉ E) ∧
      ((∀ w ∈ S, 0 ≤ w.1 ∧ 0 ≤ w.2) →
        ∀ e ∈ E, 0 ≤ e.1.1 ∧ 0 ≤ e.1.2 ∧ 0 ≤ e.2.1 ∧ 0 ≤ e.2.2) ∧
      ((∀ w ∈ S, 0 ≤ w.1 ∧ 0 ≤ w.2) →
        (0, 0) ∈ S → ((0, 1), (0, 0)) ∈ E) := by
  obtain ⟨E, hmem⟩ := exists_square_boundary_edges S
  exact ⟨E, hmem, square_boundary_edges_degree_balance hmem,
    square_boundary_edges_are_unit_steps hmem,
    square_boundary_edges_have_no_reverse hmem,
    square_boundary_edges_stay_in_nonnegative_quadrant hmem,
    square_boundary_origin_left_edge hmem⟩

end LPPDifferentiability

end
