/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.LastPassage
public import LPP_Foundations.Model.Paths.WeightConcat
import LPP_Foundations.Model.Paths.WeightZero

/-! Finite maxima over paths, and deterministic superadditivity of passage times. -/

@[expose] public section

namespace LPPDifferentiability

/-- The finite maximum dominates the weight of every admissible path. -/
theorem pathWeight_le_lastPassage (ω : Environment) {u : Lattice} {d : ℕ × ℕ}
    (p : Path u d) : pathWeight ω p ≤ lastPassage ω u d := by
  classical
  exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨p, Finset.mem_univ p, rfl⟩)

/-- There is a maximizing path for every allowed displacement. -/
theorem exists_pathWeight_eq_lastPassage (ω : Environment) (u : Lattice) (d : ℕ × ℕ) :
    ∃ p : Path u d, pathWeight ω p = lastPassage ω u d := by
  classical
  have h := Finset.max'_mem (Finset.univ.image (pathWeight ω : Path u d → ℝ))
    (Finset.Nonempty.image Finset.univ_nonempty _)
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp h
  exact ⟨p, hp⟩

/-- Passage over zero displacement collects no weight, even for signed laws. -/
@[simp] theorem lastPassage_zero (ω : Environment) (u : Lattice) :
    lastPassage ω u (0, 0) = 0 := by
  obtain ⟨p, hp⟩ := exists_pathWeight_eq_lastPassage ω u (0, 0)
  exact hp.symm.trans (pathWeight_zero ω u p)

/-- Concatenate maximizing paths; the joining vertex is collected once. -/
theorem lastPassage_superadditive (ω : Environment) (u : Lattice) (d e : ℕ × ℕ) :
    lastPassage ω u d + lastPassage ω (u + ((d.1 : ℤ), (d.2 : ℤ))) e ≤
      lastPassage ω u (d + e) := by
  obtain ⟨p, hp⟩ := exists_pathWeight_eq_lastPassage ω u d
  obtain ⟨q, hq⟩ := exists_pathWeight_eq_lastPassage ω (u + ((d.1 : ℤ), (d.2 : ℤ))) e
  calc
    lastPassage ω u d + lastPassage ω (u + ((d.1 : ℤ), (d.2 : ℤ))) e =
        pathWeight ω p + pathWeight ω q := by rw [hp, hq]
    _ = pathWeight ω (p.concat q) := (pathWeight_concat ω p q).symm
    _ ≤ lastPassage ω u (d + e) := pathWeight_le_lastPassage ω (p.concat q)

end LPPDifferentiability
