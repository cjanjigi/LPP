/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.RightmostPaths
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Tactic

/-! The finite region strictly between two rightmost paths. -/

@[expose] public section

open LPPDifferentiability

namespace LPP.Busemann

/-- The region strictly between two rightmost paths at equal absolute levels
is finite, lies in the prescribed open box, and avoids both paths at all times.
Below the upper path's initial level the upper comparison is omitted.
This constructs the region in GRS arXiv:1510.00860v1, Appendix A.4,
lines 1581–1586. -/
theorem exists_finite_rightmost_path_corridor
    (C : LPPDifferentiability.Lattice → LPPDifferentiability.Lattice → ℝ)
    (ell : ℕ) (M1 M2 : ℤ) (nN : ℕ)
    (hNorth : LPP.Busemann.rightmostCocyclePath C 0 nN = (M1, M2)) :
    ∃ R : Finset LPPDifferentiability.Lattice,
      (∀ z, z ∈ R ↔
        0 < z.1 ∧ z.2 < M2 ∧
        ∃ n : ℕ, (n : ℤ) = z.1 + z.2 ∧
          (LPP.Busemann.rightmostCocyclePath C 0 n).2 < z.2 ∧
          (n < ell ∨ z.2 <
            (LPP.Busemann.rightmostCocyclePath C (0, (ell : ℤ)) (n - ell)).2)) ∧
      (∀ z ∈ R, 0 < z.1 ∧ z.1 < M1 ∧ 0 < z.2 ∧ z.2 < M2) ∧
      (∀ m : ℕ, LPP.Busemann.rightmostCocyclePath C 0 m ∉ R ∧
        LPP.Busemann.rightmostCocyclePath C (0, (ell : ℤ)) m ∉ R) := by
  classical
  -- A step changes exactly one coordinate, increasing the level by one.
  have hstep (x : Lattice) (n : ℕ) :
      rightmostCocyclePath C x (n + 1) = rightmostCocyclePath C x n + (1, 0) ∨
      rightmostCocyclePath C x (n + 1) = rightmostCocyclePath C x n + (0, 1) := by
    simpa [rightmostCocyclePath, Function.iterate_succ_apply'] using
      rightmostCocycleSuccessor_step C (rightmostCocyclePath C x n)
  have hlevel (x : Lattice) (n : ℕ) :
      (rightmostCocyclePath C x n).1 + (rightmostCocyclePath C x n).2 =
        x.1 + x.2 + (n : ℤ) := by
    induction n with
    | zero => simp [rightmostCocyclePath]
    | succ n ih =>
      rcases hstep x n with h | h <;>
        simp only [h, Prod.fst_add, Prod.snd_add, Nat.cast_succ] <;> omega
  have hfst (x : Lattice) : Monotone (fun n => (rightmostCocyclePath C x n).1) := by
    apply monotone_nat_of_le_succ
    intro n
    rcases hstep x n with h | h <;> simp only [h, Prod.fst_add] <;> omega
  have hsnd (x : Lattice) : Monotone (fun n => (rightmostCocyclePath C x n).2) := by
    apply monotone_nat_of_le_succ
    intro n
    rcases hstep x n with h | h <;> simp only [h, Prod.snd_add] <;> omega
  let P : Lattice → Prop := fun z =>
    0 < z.1 ∧ z.2 < M2 ∧
      ∃ n : ℕ, (n : ℤ) = z.1 + z.2 ∧
        (rightmostCocyclePath C 0 n).2 < z.2 ∧
        (n < ell ∨ z.2 < (rightmostCocyclePath C (0, (ell : ℤ)) (n - ell)).2)
  -- The source condition itself puts every site in the finite rectangle.
  have hbox (z : Lattice) (hz : P z) :
      0 < z.1 ∧ z.1 < M1 ∧ 0 < z.2 ∧ z.2 < M2 := by
    rcases hz with ⟨hz1, hz2, n, hn, hbelow, _⟩
    have hnonneg : 0 ≤ (rightmostCocyclePath C 0 n).2 := by
      have h := hsnd 0 (Nat.zero_le n)
      simpa [rightmostCocyclePath] using h
    have hnN : n < nN := by
      by_contra h
      have h := hsnd 0 (show nN ≤ n by omega)
      dsimp only at h
      rw [hNorth] at h
      simp only at h
      omega
    have hfirst := hfst 0 (Nat.le_of_lt hnN)
    dsimp only at hfirst
    rw [hNorth] at hfirst
    simp only at hfirst
    have hlev := hlevel 0 n
    simp only [Prod.fst_zero, Prod.snd_zero, zero_add] at hlev
    exact ⟨hz1, by omega, by omega, hz2⟩
  let R : Finset Lattice :=
    ((Finset.Icc (1 : ℤ) (M1 - 1)).product (Finset.Icc (1 : ℤ) (M2 - 1))).filter P
  have hmem (z : Lattice) : z ∈ R ↔ P z := by
    constructor
    · intro hz
      exact (Finset.mem_filter.mp hz).2
    · intro hz
      have hb := hbox z hz
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_product.mpr
        exact ⟨Finset.mem_Icc.mpr (by omega), Finset.mem_Icc.mpr (by omega)⟩
      · exact hz
  refine ⟨R, ?_, ?_, ?_⟩
  · intro z
    exact hmem z
  · intro z hz
    exact hbox z ((hmem z).mp hz)
  · intro m
    constructor
    · intro hz
      have hp := (hmem _).mp hz
      rcases hp with ⟨_, _, n, hn, hbelow, _⟩
      have hl := hlevel 0 m
      simp only [Prod.fst_zero, Prod.snd_zero, zero_add] at hl
      have hnm : n = m := by omega
      subst n
      exact (lt_irrefl _) hbelow
    · intro hz
      have hp := (hmem _).mp hz
      rcases hp with ⟨_, _, n, hn, _, hupper⟩
      have hl := hlevel (0, (ell : ℤ)) m
      simp only [zero_add] at hl
      have hnm : n = ell + m := by omega
      have hnot : ¬ n < ell := by omega
      rcases hupper with hlt | hlt
      · exact hnot hlt
      · have hsub : n - ell = m := by omega
        rw [hsub] at hlt
        exact (lt_irrefl _) hlt

end LPP.Busemann
