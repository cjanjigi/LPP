/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Paths.Geometry
public import LPP_Foundations.Model.LastPassage.Basic

/-! Axis paths and terminal-excluded axis passage sums. -/

@[expose] public section

open scoped BigOperators

namespace LPPDifferentiability

/-- Every horizontal path has the prescribed vertex at every local time. -/
theorem Path.vertex_horizontal {u : Lattice} {n : ℕ} (p : Path u (n, 0))
    (i : Fin (n + 0 + 1)) :
    p.vertex i = (u.1 + (i.val : ℤ), u.2) := by
  have hr := p.vertex_mem_Icc i
  have hl := p.level i
  have hs : (p.vertex i).2 = u.2 := by
    have hlo := hr.1.2
    have hhi := hr.2.2
    simp only [Prod.snd_add, Nat.cast_zero, add_zero] at hhi
    omega
  apply Prod.ext
  · dsimp only at hl
    omega
  · exact hs

/-- Every vertical path has the prescribed vertex at every local time. -/
theorem Path.vertex_vertical {u : Lattice} {n : ℕ} (p : Path u (0, n))
    (i : Fin (0 + n + 1)) :
    p.vertex i = (u.1, u.2 + (i.val : ℤ)) := by
  have hr := p.vertex_mem_Icc i
  have hl := p.level i
  have hs : (p.vertex i).1 = u.1 := by
    have hlo := hr.1.1
    have hhi := hr.2.1
    simp only [Prod.fst_add, Nat.cast_zero, add_zero] at hhi
    omega
  apply Prod.ext
  · exact hs
  · dsimp only at hl
    omega

/-- Horizontal path weights omit the terminal vertex, including at length zero. -/
theorem pathWeight_horizontal (ω : Environment) {u : Lattice} {n : ℕ}
    (p : Path u (n, 0)) :
    pathWeight ω p = ∑ i : Fin n, ω (u.1 + (i.val : ℤ), u.2) := by
  unfold pathWeight
  simp only [Path.vertex_horizontal, Fin.val_castSucc, Nat.add_zero]

/-- Vertical path weights omit the terminal vertex, including at length zero. -/
theorem pathWeight_vertical (ω : Environment) {u : Lattice} {n : ℕ}
    (p : Path u (0, n)) :
    pathWeight ω p = ∑ i : Fin n, ω (u.1, u.2 + (i.val : ℤ)) := by
  unfold pathWeight
  simp only [Path.vertex_vertical, Fin.val_castSucc]
  change (∑ i : Fin (0 + n), ω (u.1, u.2 + (i.val : ℤ))) = _
  exact Fintype.sum_equiv (finCongr (Nat.zero_add n)) _ _ (fun _ => rfl)

/-- The horizontal last passage equals the unique axis sum for signed weights. -/
theorem lastPassage_horizontal (ω : Environment) (u : Lattice) (n : ℕ) :
    lastPassage ω u (n, 0) = ∑ i : Fin n, ω (u.1 + (i.val : ℤ), u.2) := by
  obtain ⟨p, hp⟩ := exists_pathWeight_eq_lastPassage ω u (n, 0)
  exact hp.symm.trans (pathWeight_horizontal ω p)

/-- The vertical last passage equals the unique axis sum for signed weights. -/
theorem lastPassage_vertical (ω : Environment) (u : Lattice) (n : ℕ) :
    lastPassage ω u (0, n) = ∑ i : Fin n, ω (u.1, u.2 + (i.val : ℤ)) := by
  obtain ⟨p, hp⟩ := exists_pathWeight_eq_lastPassage ω u (0, n)
  exact hp.symm.trans (pathWeight_vertical ω p)

end LPPDifferentiability
