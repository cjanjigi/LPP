/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Process.OneSidedBoundaryPotential

/-! Conditional finite-order consequences of the one-sided boundary maximum. -/

@[expose] public section

open LPPDifferentiability

namespace LPP.Busemann

/-- If the north-boundary passage is strictly below the cocycle value, then the
east-boundary passage equals it (GRS 1510.00859v2, Section 5.2, Theorem 6.1,
Step 1). -/
theorem east_boundary_passage_eq_cocycle_of_north_deficit
    (ω : Environment) (C : Lattice → Lattice → ℝ)
    (hC : is_additive C) (hrec : recovers_environment ω C)
    (x : Lattice) (d : ℕ × ℕ) :
    let v : Lattice := x + ((d.1 : ℤ), (d.2 : ℤ))
    let N : Environment :=
      fun z => if z.2 = v.2 ∧ z.1 < v.1 then C z (z + (1, 0)) else ω z
    let E : Environment :=
      fun z => if z.1 = v.1 ∧ z.2 < v.2 then C z (z + (0, 1)) else ω z
    lastPassage N x d < C x v → lastPassage E x d = C x v := by
  intro v N E hN
  -- The identity expresses the cocycle value as the larger passage.
  have hmax : C x v = max (lastPassage N x d) (lastPassage E x d) :=
    cocycle_potential_eq_max_one_sided_boundary_passages ω C hC hrec x d
  -- If north is the larger term, it contradicts the strict deficit.
  rcases le_total (lastPassage N x d) (lastPassage E x d) with hNE | hEN
  · rw [max_eq_right hNE] at hmax
    exact hmax.symm
  · rw [max_eq_left hEN] at hmax
    have hneq : lastPassage N x d ≠ C x v := ne_of_lt hN
    exact False.elim (hneq hmax.symm)

/-- If the east-boundary passage is strictly below the cocycle value, then the
north-boundary passage equals it (GRS 1510.00859v2, Section 5.2, Theorem 6.1,
Step 1). -/
theorem north_boundary_passage_eq_cocycle_of_east_deficit
    (ω : Environment) (C : Lattice → Lattice → ℝ)
    (hC : is_additive C) (hrec : recovers_environment ω C)
    (x : Lattice) (d : ℕ × ℕ) :
    let v : Lattice := x + ((d.1 : ℤ), (d.2 : ℤ))
    let N : Environment :=
      fun z => if z.2 = v.2 ∧ z.1 < v.1 then C z (z + (1, 0)) else ω z
    let E : Environment :=
      fun z => if z.1 = v.1 ∧ z.2 < v.2 then C z (z + (0, 1)) else ω z
    lastPassage E x d < C x v → lastPassage N x d = C x v := by
  intro v N E hE
  -- The same identity handles the east deficit.
  have hmax : C x v = max (lastPassage N x d) (lastPassage E x d) :=
    cocycle_potential_eq_max_one_sided_boundary_passages ω C hC hrec x d
  -- If east is the larger term, it contradicts the strict deficit.
  rcases le_total (lastPassage E x d) (lastPassage N x d) with hEN | hNE
  · rw [max_eq_left hEN] at hmax
    exact hmax.symm
  · rw [max_eq_right hNE] at hmax
    have hneq : lastPassage E x d ≠ C x v := ne_of_lt hE
    exact False.elim (hneq hmax.symm)

end LPP.Busemann
