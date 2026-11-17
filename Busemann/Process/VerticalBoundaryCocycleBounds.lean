/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Process.FiniteBoundaryDeficit
public import LPP_Foundations.Model.LastPassage.BoundaryGradientComparison

/-! Conditional finite vertical passage comparisons from boundary deficits. -/

@[expose] public section

open LPPDifferentiability

namespace LPP.Busemann

/-- Two east-boundary deficits force the vertical cocycle increment below the
ordinary passage difference (GRS 1510.00859v2, Theorem 6.1, Step 1). -/
theorem vertical_passage_difference_ge_cocycle_of_east_deficits
    (ω : Environment) (C : Lattice → Lattice → ℝ)
    (hC : is_additive C) (hrec : recovers_environment ω C)
    (x : Lattice) (a b : ℕ) :
    let v : Lattice := x + ((a : ℤ), ((b + 2 : ℕ) : ℤ))
    let E : Environment := fun z =>
      if z.1 = v.1 ∧ z.2 < v.2 then C z (z + (0, 1)) else ω z
    lastPassage E x (a, b + 2) < C x v →
    lastPassage E (x + (0, 1)) (a, b + 1) < C (x + (0, 1)) v →
    C x (x + (0, 1)) ≤
      lastPassage ω x (a, b + 1) - lastPassage ω (x + (0, 1)) (a, b) := by
  intro v E hfirst hchild
  let child : Lattice := x + (0, 1)
  let N : Environment := fun z =>
    if z.2 = v.2 ∧ z.1 < v.1 then C z (z + (1, 0)) else ω z
  -- The child rectangle and comparison field have the same terminal site.
  have hchildTerminal : child + ((a : ℤ), (((b + 1 : ℕ) : ℤ))) = v := by
    apply Prod.ext
    · simp only [child, v, Prod.fst_add]
      omega
    · simp only [child, v, Prod.snd_add]
      omega
  have hcomparisonHeight :
      (x + ((a : ℤ), (((b + 1 : ℕ) : ℤ)))).2 + 1 = v.2 := by
    simp only [v, Prod.snd_add]
    omega
  have hcomparisonWidth :
      (x + ((a : ℤ), (((b + 1 : ℕ) : ℤ)))).1 = v.1 := by
    simp only [v, Prod.fst_add]
  -- Each east deficit selects the north passage to the common terminal.
  have hNfirst : lastPassage N x (a, b + 2) = C x v := by
    exact north_boundary_passage_eq_cocycle_of_east_deficit
      ω C hC hrec x (a, b + 2) hfirst
  have hNchild : lastPassage N child (a, b + 1) = C child v := by
    have h := north_boundary_passage_eq_cocycle_of_east_deficit
      ω C hC hrec child (a, b + 1)
    rw [hchildTerminal] at h
    exact h (by simpa only [hchildTerminal] using hchild)
  have hcomparison :=
    (LPP.vertical_passage_difference_boundary_comparison ω C x a b).1
  have hNcomparison :
      lastPassage N x (a, b + 2) - lastPassage N child (a, b + 1) ≤
        lastPassage ω x (a, b + 1) - lastPassage ω child (a, b) := by
    simpa only [N, child, hcomparisonHeight, hcomparisonWidth] using hcomparison
  -- Additivity identifies the difference of the selected passages.
  have hCedge : C x v - C child v = C x child := by
    have hadd := hC x child v
    rw [← hadd]
    simp
  rw [hNfirst, hNchild, hCedge] at hNcomparison
  simpa only [child] using hNcomparison

/-- Two north-boundary deficits force the vertical cocycle increment above the
ordinary passage difference (GRS 1510.00859v2, Theorem 6.1, Step 1). -/
theorem vertical_passage_difference_le_cocycle_of_north_deficits
    (ω : Environment) (C : Lattice → Lattice → ℝ)
    (hC : is_additive C) (hrec : recovers_environment ω C)
    (x : Lattice) (a b : ℕ) :
    let v : Lattice := x + (((a + 1 : ℕ) : ℤ), ((b + 1 : ℕ) : ℤ))
    let N : Environment := fun z =>
      if z.2 = v.2 ∧ z.1 < v.1 then C z (z + (1, 0)) else ω z
    lastPassage N x (a + 1, b + 1) < C x v →
    lastPassage N (x + (0, 1)) (a + 1, b) < C (x + (0, 1)) v →
    lastPassage ω x (a, b + 1) - lastPassage ω (x + (0, 1)) (a, b) ≤
      C x (x + (0, 1)) := by
  intro v N hfirst hchild
  let child : Lattice := x + (0, 1)
  let E : Environment := fun z =>
    if z.1 = v.1 ∧ z.2 < v.2 then C z (z + (0, 1)) else ω z
  -- The child rectangle and comparison field have the same terminal site.
  have hchildTerminal : child + ((((a + 1 : ℕ) : ℤ)), (b : ℤ)) = v := by
    apply Prod.ext
    · simp only [child, v, Prod.fst_add]
      omega
    · simp only [child, v, Prod.snd_add]
      omega
  have hcomparisonHeight :
      (x + ((a : ℤ), (((b + 1 : ℕ) : ℤ)))).2 = v.2 := by
    simp only [v, Prod.snd_add]
  have hcomparisonWidth :
      (x + ((a : ℤ), (((b + 1 : ℕ) : ℤ)))).1 + 1 = v.1 := by
    simp only [v, Prod.fst_add]
    omega
  -- Each north deficit selects the east passage to the common terminal.
  have hEfirst : lastPassage E x (a + 1, b + 1) = C x v := by
    exact east_boundary_passage_eq_cocycle_of_north_deficit
      ω C hC hrec x (a + 1, b + 1) hfirst
  have hEchild : lastPassage E child (a + 1, b) = C child v := by
    have h := east_boundary_passage_eq_cocycle_of_north_deficit
      ω C hC hrec child (a + 1, b)
    rw [hchildTerminal] at h
    exact h (by simpa only [hchildTerminal] using hchild)
  have hcomparison :=
    (LPP.vertical_passage_difference_boundary_comparison ω C x a b).2
  have hEcomparison :
      lastPassage ω x (a, b + 1) - lastPassage ω child (a, b) ≤
        lastPassage E x (a + 1, b + 1) - lastPassage E child (a + 1, b) := by
    simpa only [E, child, hcomparisonHeight, hcomparisonWidth] using hcomparison
  -- Additivity identifies the difference of the selected passages.
  have hCedge : C x v - C child v = C x child := by
    have hadd := hC x child v
    rw [← hadd]
    simp
  rw [hEfirst, hEchild, hCedge] at hEcomparison
  simpa only [child] using hEcomparison

end LPP.Busemann
