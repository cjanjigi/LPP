/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.Definitions.RightmostCocyclePath
import Mathlib.Logic.Function.Iterate

/-! Deterministic translation covariance for the rightmost cocycle path. -/

@[expose] public section
open LPPDifferentiability

namespace LPP.Busemann

/-- Translating every cocycle edge translates the chosen rightmost successor.
GRS, arXiv:1510.00860v1, Appendix A. -/
theorem rightmostCocycleSuccessor_translate
    (C D : Lattice → Lattice → ℝ) (z : Lattice)
    (hD : ∀ x y, D x y = C (x + z) (y + z)) (x : Lattice) :
    rightmostCocycleSuccessor D x + z = rightmostCocycleSuccessor C (x + z) := by
  let e₁ : Lattice := ((1 : ℤ), (0 : ℤ))
  let e₂ : Lattice := ((0 : ℤ), (1 : ℤ))
  have hEastTranslate : (x + e₁) + z = (x + z) + e₁ := by
    ext <;> ring
  have hNorthTranslate : (x + e₂) + z = (x + z) + e₂ := by
    ext <;> ring
  have hEast : D x (x + e₁) = C (x + z) ((x + z) + e₁) := by
    rw [hD x (x + e₁), hEastTranslate]
  have hNorth : D x (x + e₂) = C (x + z) ((x + z) + e₂) := by
    rw [hD x (x + e₂), hNorthTranslate]
  have hCompare :
      D x (x + e₁) ≤ D x (x + e₂) ↔
        C (x + z) ((x + z) + e₁) ≤ C (x + z) ((x + z) + e₂) := by
    rw [hEast, hNorth]
  by_cases h : D x (x + e₁) ≤ D x (x + e₂)
  · have hTranslated := hCompare.mp h
    calc
      rightmostCocycleSuccessor D x + z = (x + e₁) + z := by
        simp [rightmostCocycleSuccessor, e₁, e₂, h]
      _ = (x + z) + e₁ := hEastTranslate
      _ = rightmostCocycleSuccessor C (x + z) := by
        simp [rightmostCocycleSuccessor, e₁, e₂, hTranslated]
  · have hTranslated :
        ¬ C (x + z) ((x + z) + e₁) ≤ C (x + z) ((x + z) + e₂) := by
      intro hC
      exact h (hCompare.mpr hC)
    calc
      rightmostCocycleSuccessor D x + z = (x + e₂) + z := by
        simp [rightmostCocycleSuccessor, e₁, e₂, h]
      _ = (x + z) + e₂ := hNorthTranslate
      _ = rightmostCocycleSuccessor C (x + z) := by
        simp [rightmostCocycleSuccessor, e₁, e₂, hTranslated]

/-- The translated successor identity gives the same path from the translated start at every time.
GRS, arXiv:1510.00860v1, Appendix A. -/
theorem rightmostCocyclePath_translate
    (C D : Lattice → Lattice → ℝ) (z : Lattice)
    (hD : ∀ x y, D x y = C (x + z) (y + z)) (x : Lattice) (n : ℕ) :
    rightmostCocyclePath D x n + z = rightmostCocyclePath C (x + z) n := by
  have hSemiconj :
      Function.Semiconj (fun y : Lattice => y + z)
        (rightmostCocycleSuccessor D) (rightmostCocycleSuccessor C) := by
    intro y
    exact rightmostCocycleSuccessor_translate C D z hD y
  simpa only [rightmostCocyclePath] using
    (Function.Semiconj.iterate_right hSemiconj n x)

end LPP.Busemann
