/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Union
import Lean.Elab.Tactic.Omega

/-!
# Finite directed square boundaries

The oriented boundary of a finite family of lattice squares is the finite
set of sides whose neighboring square is absent from the family.
-/

public section

namespace LPPDifferentiability

/-- A finite family of lattice sites has a finite directed boundary with the
literal four-side membership rule for counterclockwise unit squares. -/
theorem exists_square_boundary_edges (S : Finset (Int × Int)) :
    ∃ E : Finset (((Int × Int) × (Int × Int))),
      ∀ e, e ∈ E ↔ ∃ w, w ∈ S ∧
        ((e = ((w.1, w.2), (w.1 + 1, w.2)) ∧ (w.1, w.2 - 1) ∉ S) ∨
         (e = ((w.1 + 1, w.2), (w.1 + 1, w.2 + 1)) ∧ (w.1 + 1, w.2) ∉ S) ∨
         (e = ((w.1 + 1, w.2 + 1), (w.1, w.2 + 1)) ∧ (w.1, w.2 + 1) ∉ S) ∨
         (e = ((w.1, w.2 + 1), (w.1, w.2)) ∧ (w.1 - 1, w.2) ∉ S)) := by
  classical
  let bottom : Finset (((Int × Int) × (Int × Int))) :=
    (S.filter fun w => (w.1, w.2 - 1) ∉ S).image
      (fun w => ((w.1, w.2), (w.1 + 1, w.2)))
  let right : Finset (((Int × Int) × (Int × Int))) :=
    (S.filter fun w => (w.1 + 1, w.2) ∉ S).image
      (fun w => ((w.1 + 1, w.2), (w.1 + 1, w.2 + 1)))
  let top : Finset (((Int × Int) × (Int × Int))) :=
    (S.filter fun w => (w.1, w.2 + 1) ∉ S).image
      (fun w => ((w.1 + 1, w.2 + 1), (w.1, w.2 + 1)))
  let left : Finset (((Int × Int) × (Int × Int))) :=
    (S.filter fun w => (w.1 - 1, w.2) ∉ S).image
      (fun w => ((w.1, w.2 + 1), (w.1, w.2)))
  refine ⟨bottom ∪ (right ∪ (top ∪ left)), ?_⟩
  intro e
  simp only [Finset.mem_union, bottom, right, top, left, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro (⟨w, ⟨hw, hout⟩, he⟩ | ⟨w, ⟨hw, hout⟩, he⟩ |
      ⟨w, ⟨hw, hout⟩, he⟩ | ⟨w, ⟨hw, hout⟩, he⟩)
    · exact ⟨w, hw, Or.inl ⟨he.symm, hout⟩⟩
    · exact ⟨w, hw, Or.inr (Or.inl ⟨he.symm, hout⟩)⟩
    · exact ⟨w, hw, Or.inr (Or.inr (Or.inl ⟨he.symm, hout⟩))⟩
    · exact ⟨w, hw, Or.inr (Or.inr (Or.inr ⟨he.symm, hout⟩))⟩
  · rintro ⟨w, hw, hside⟩
    rcases hside with ⟨he, hout⟩ | ⟨he, hout⟩ | ⟨he, hout⟩ | ⟨he, hout⟩
    · exact Or.inl ⟨w, ⟨hw, hout⟩, he.symm⟩
    · exact Or.inr (Or.inl ⟨w, ⟨hw, hout⟩, he.symm⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨w, ⟨hw, hout⟩, he.symm⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨w, ⟨hw, hout⟩, he.symm⟩))

/-- Every retained side is one of the four directed unit steps. -/
theorem square_boundary_edges_are_unit_steps
    {S : Finset (Int × Int)} {E : Finset (((Int × Int) × (Int × Int)))}
    (hmem : ∀ e, e ∈ E ↔ ∃ w, w ∈ S ∧
      ((e = ((w.1, w.2), (w.1 + 1, w.2)) ∧ (w.1, w.2 - 1) ∉ S) ∨
       (e = ((w.1 + 1, w.2), (w.1 + 1, w.2 + 1)) ∧ (w.1 + 1, w.2) ∉ S) ∨
       (e = ((w.1 + 1, w.2 + 1), (w.1, w.2 + 1)) ∧ (w.1, w.2 + 1) ∉ S) ∨
       (e = ((w.1, w.2 + 1), (w.1, w.2)) ∧ (w.1 - 1, w.2) ∉ S))) :
    ∀ e ∈ E,
      (e.2.1 = e.1.1 + 1 ∧ e.2.2 = e.1.2) ∨
      (e.2.1 = e.1.1 ∧ e.2.2 = e.1.2 + 1) ∨
      (e.2.1 = e.1.1 - 1 ∧ e.2.2 = e.1.2) ∨
      (e.2.1 = e.1.1 ∧ e.2.2 = e.1.2 - 1) := by
  intro e he
  rcases (hmem e).mp he with ⟨w, hw, hside⟩
  rcases hside with ⟨heq, _⟩ | ⟨heq, _⟩ | ⟨heq, _⟩ | ⟨heq, _⟩
  · rw [heq]
    simp
  · rw [heq]
    simp
  · rw [heq]
    simp
  · rw [heq]
    simp

/-- A retained directed side never has its reverse in the remaining boundary. -/
theorem square_boundary_edges_have_no_reverse
    {S : Finset (Int × Int)} {E : Finset (((Int × Int) × (Int × Int)))}
    (hmem : ∀ e, e ∈ E ↔ ∃ w, w ∈ S ∧
      ((e = ((w.1, w.2), (w.1 + 1, w.2)) ∧ (w.1, w.2 - 1) ∉ S) ∨
       (e = ((w.1 + 1, w.2), (w.1 + 1, w.2 + 1)) ∧ (w.1 + 1, w.2) ∉ S) ∨
       (e = ((w.1 + 1, w.2 + 1), (w.1, w.2 + 1)) ∧ (w.1, w.2 + 1) ∉ S) ∨
       (e = ((w.1, w.2 + 1), (w.1, w.2)) ∧ (w.1 - 1, w.2) ∉ S))) :
    ∀ e ∈ E, (e.2, e.1) ∉ E := by
  intro e he hreverse
  rcases (hmem e).mp he with ⟨w, hw, hside⟩
  rcases (hmem (e.2, e.1)).mp hreverse with ⟨w', hw', hside'⟩
  rcases hside with ⟨heq, hout⟩ | ⟨heq, hout⟩ | ⟨heq, hout⟩ | ⟨heq, hout⟩
  · rcases hside' with ⟨heq', _⟩ | ⟨heq', _⟩ | ⟨heq', _⟩ | ⟨heq', _⟩
    · have : False := by rw [heq] at heq'; simp only [Prod.mk.injEq] at heq'; omega
      exact this.elim
    · have : False := by rw [heq] at heq'; simp only [Prod.mk.injEq] at heq'; omega
      exact this.elim
    · rw [heq] at heq'
      have hwEq : w' = (w.1, w.2 - 1) := by
        apply Prod.ext
        · rcases Prod.mk.inj heq' with ⟨hstart, _⟩
          rcases Prod.mk.inj hstart with ⟨hx, _⟩
          omega
        · rcases Prod.mk.inj heq' with ⟨hstart, _⟩
          rcases Prod.mk.inj hstart with ⟨_, hy⟩
          omega
      rw [hwEq] at hw'
      exact hout hw'
    · have : False := by rw [heq] at heq'; simp only [Prod.mk.injEq] at heq'; omega
      exact this.elim
  · rcases hside' with ⟨heq', _⟩ | ⟨heq', _⟩ | ⟨heq', _⟩ | ⟨heq', _⟩
    · have : False := by rw [heq] at heq'; simp only [Prod.mk.injEq] at heq'; omega
      exact this.elim
    · have : False := by rw [heq] at heq'; simp only [Prod.mk.injEq] at heq'; omega
      exact this.elim
    · have : False := by rw [heq] at heq'; simp only [Prod.mk.injEq] at heq'; omega
      exact this.elim
    · rw [heq] at heq'
      have hwEq : w' = (w.1 + 1, w.2) := by
        apply Prod.ext
        · rcases Prod.mk.inj heq' with ⟨hstart, _⟩
          rcases Prod.mk.inj hstart with ⟨hx, _⟩
          omega
        · rcases Prod.mk.inj heq' with ⟨hstart, _⟩
          rcases Prod.mk.inj hstart with ⟨_, hy⟩
          omega
      rw [hwEq] at hw'
      exact hout hw'
  · rcases hside' with ⟨heq', _⟩ | ⟨heq', _⟩ | ⟨heq', _⟩ | ⟨heq', _⟩
    · rw [heq] at heq'
      have hwEq : w' = (w.1, w.2 + 1) := by
        apply Prod.ext
        · rcases Prod.mk.inj heq' with ⟨hstart, _⟩
          rcases Prod.mk.inj hstart with ⟨hx, _⟩
          omega
        · rcases Prod.mk.inj heq' with ⟨hstart, _⟩
          rcases Prod.mk.inj hstart with ⟨_, hy⟩
          omega
      rw [hwEq] at hw'
      exact hout hw'
    · have : False := by rw [heq] at heq'; simp only [Prod.mk.injEq] at heq'; omega
      exact this.elim
    · have : False := by rw [heq] at heq'; simp only [Prod.mk.injEq] at heq'; omega
      exact this.elim
    · have : False := by rw [heq] at heq'; simp only [Prod.mk.injEq] at heq'; omega
      exact this.elim
  · rcases hside' with ⟨heq', _⟩ | ⟨heq', _⟩ | ⟨heq', _⟩ | ⟨heq', _⟩
    · have : False := by rw [heq] at heq'; simp only [Prod.mk.injEq] at heq'; omega
      exact this.elim
    · rw [heq] at heq'
      have hwEq : w' = (w.1 - 1, w.2) := by
        apply Prod.ext
        · rcases Prod.mk.inj heq' with ⟨hstart, _⟩
          rcases Prod.mk.inj hstart with ⟨hx, _⟩
          omega
        · rcases Prod.mk.inj heq' with ⟨hstart, _⟩
          rcases Prod.mk.inj hstart with ⟨_, hy⟩
          omega
      rw [hwEq] at hw'
      exact hout hw'
    · have : False := by rw [heq] at heq'; simp only [Prod.mk.injEq] at heq'; omega
      exact this.elim
    · have : False := by rw [heq] at heq'; simp only [Prod.mk.injEq] at heq'; omega
      exact this.elim

/-- If the sites lie in the nonnegative quadrant, so do all boundary vertices. -/
theorem square_boundary_edges_stay_in_nonnegative_quadrant
    {S : Finset (Int × Int)} {E : Finset (((Int × Int) × (Int × Int)))}
    (hmem : ∀ e, e ∈ E ↔ ∃ w, w ∈ S ∧
      ((e = ((w.1, w.2), (w.1 + 1, w.2)) ∧ (w.1, w.2 - 1) ∉ S) ∨
       (e = ((w.1 + 1, w.2), (w.1 + 1, w.2 + 1)) ∧ (w.1 + 1, w.2) ∉ S) ∨
       (e = ((w.1 + 1, w.2 + 1), (w.1, w.2 + 1)) ∧ (w.1, w.2 + 1) ∉ S) ∨
       (e = ((w.1, w.2 + 1), (w.1, w.2)) ∧ (w.1 - 1, w.2) ∉ S)))
    (hquadrant : ∀ w ∈ S, 0 ≤ w.1 ∧ 0 ≤ w.2) :
    ∀ e ∈ E,
      0 ≤ e.1.1 ∧ 0 ≤ e.1.2 ∧ 0 ≤ e.2.1 ∧ 0 ≤ e.2.2 := by
  intro e he
  rcases (hmem e).mp he with ⟨w, hw, hside⟩
  obtain ⟨hx, hy⟩ := hquadrant w hw
  rcases hside with ⟨heq, _⟩ | ⟨heq, _⟩ | ⟨heq, _⟩ | ⟨heq, _⟩
  · rw [heq]
    simp
    omega
  · rw [heq]
    simp
    omega
  · rw [heq]
    simp
    omega
  · rw [heq]
    simp
    omega

/-- For a nonnegative family containing the origin, the actual left side of
the origin square is retained in the directed boundary. -/
theorem square_boundary_origin_left_edge
    {S : Finset (Int × Int)} {E : Finset (((Int × Int) × (Int × Int)))}
    (hmem : ∀ e, e ∈ E ↔ ∃ w, w ∈ S ∧
      ((e = ((w.1, w.2), (w.1 + 1, w.2)) ∧ (w.1, w.2 - 1) ∉ S) ∨
       (e = ((w.1 + 1, w.2), (w.1 + 1, w.2 + 1)) ∧ (w.1 + 1, w.2) ∉ S) ∨
       (e = ((w.1 + 1, w.2 + 1), (w.1, w.2 + 1)) ∧ (w.1, w.2 + 1) ∉ S) ∨
       (e = ((w.1, w.2 + 1), (w.1, w.2)) ∧ (w.1 - 1, w.2) ∉ S)))
    (hquadrant : ∀ w ∈ S, 0 ≤ w.1 ∧ 0 ≤ w.2)
    (hzero : (0, 0) ∈ S) : ((0, 1), (0, 0)) ∈ E := by
  apply (hmem _).2
  have hleft : (-1, 0) ∉ S := by
    intro hneg
    have := (hquadrant (-1, 0) hneg).1
    omega
  refine ⟨(0, 0), hzero, Or.inr (Or.inr (Or.inr ⟨?_, hleft⟩))⟩
  simp

end LPPDifferentiability

end
