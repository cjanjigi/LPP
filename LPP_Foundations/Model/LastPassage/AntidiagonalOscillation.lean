/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Paths.CollectedLevels
public import LPP_Foundations.Model.LastPassage.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-! Finite-box locality and whole-antidiagonal oscillation of passage maxima. -/

@[expose] public section

open scoped BigOperators

namespace LPPDifferentiability

/-- Only collected sites in the finite endpoint box matter to a path score. -/
theorem pathWeight_eq_of_eqOn_collected_box {ω η : Environment} {d : ℕ × ℕ}
    (h : ∀ z ∈ Set.Icc (0 : Lattice) ((d.1 : ℤ), (d.2 : ℤ)),
      z.1 + z.2 < ((d.1 + d.2 : ℕ) : ℤ) → ω z = η z) (p : Path 0 d) :
    pathWeight ω p = pathWeight η p := by
  apply Finset.sum_congr rfl
  intro i _
  have hi := p.collected_mem_box (p.vertex_mem_collectedSites i)
  exact h _ hi.1 hi.2

/-- Equality on the finite collected box preserves the finite maximum. -/
theorem lastPassage_eq_of_eqOn_collected_box {ω η : Environment} {d : ℕ × ℕ}
    (h : ∀ z ∈ Set.Icc (0 : Lattice) ((d.1 : ℤ), (d.2 : ℤ)),
      z.1 + z.2 < ((d.1 + d.2 : ℕ) : ℤ) → ω z = η z) :
    lastPassage ω 0 d = lastPassage η 0 d := by
  apply le_antisymm
  · obtain ⟨p, hp⟩ := exists_pathWeight_eq_lastPassage ω 0 d
    rw [← hp, pathWeight_eq_of_eqOn_collected_box h p]
    exact pathWeight_le_lastPassage η p
  · obtain ⟨p, hp⟩ := exists_pathWeight_eq_lastPassage η 0 d
    rw [← hp, ← pathWeight_eq_of_eqOn_collected_box h p]
    exact pathWeight_le_lastPassage ω p

/-- Replacing one level changes exactly the term at its local time. -/
theorem pathWeight_sub_eq_level {ω η : Environment} {d : ℕ × ℕ}
    (k : Fin (d.1 + d.2))
    (h : ∀ z : Lattice, z.1 + z.2 ≠ (k.val : ℤ) → ω z = η z)
    (p : Path 0 d) :
    pathWeight ω p - pathWeight η p =
      ω (p.vertex k.castSucc) - η (p.vertex k.castSucc) := by
  classical
  unfold pathWeight
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_eq_single k
  · intro j _ hj
    have hlevel : (p.vertex j.castSucc).1 + (p.vertex j.castSucc).2 ≠ (k.val : ℤ) := by
      rw [p.collected_level j]
      intro heq
      exact hj (Fin.ext (by omega))
    rw [h _ hlevel, sub_self]
  · intro hk
    exact (hk (Finset.mem_univ k)).elim

/-- Pointwise bounds and agreement off one level bound every change in a path score. -/
theorem abs_pathWeight_sub_le_two_mul {ω η : Environment} {d : ℕ × ℕ}
    {L : ℝ} (hω : ∀ z, |ω z| ≤ L) (hη : ∀ z, |η z| ≤ L)
    (k : Fin (d.1 + d.2))
    (h : ∀ z : Lattice, z.1 + z.2 ≠ (k.val : ℤ) → ω z = η z)
    (p : Path 0 d) : |pathWeight ω p - pathWeight η p| ≤ 2 * L := by
  rw [pathWeight_sub_eq_level k h p]
  calc
    |ω (p.vertex k.castSucc) - η (p.vertex k.castSucc)| ≤
        |ω (p.vertex k.castSucc)| + |η (p.vertex k.castSucc)| := abs_sub _ _
    _ ≤ L + L := add_le_add (hω _) (hη _)
    _ = 2 * L := (two_mul L).symm

/-- Whole-level replacement changes the maximum by at most twice the bound.
The two comparisons use separate maximizing paths, allowing the winner to change. -/
theorem abs_lastPassage_sub_le_two_mul {ω η : Environment} {d : ℕ × ℕ}
    {L : ℝ} (hω : ∀ z, |ω z| ≤ L) (hη : ∀ z, |η z| ≤ L)
    (k : Fin (d.1 + d.2))
    (h : ∀ z : Lattice, z.1 + z.2 ≠ (k.val : ℤ) → ω z = η z) :
    |lastPassage ω 0 d - lastPassage η 0 d| ≤ 2 * L := by
  apply abs_le.mpr
  constructor
  · obtain ⟨p, hp⟩ := exists_pathWeight_eq_lastPassage η 0 d
    have hb := (abs_le.mp (abs_pathWeight_sub_le_two_mul hω hη k h p)).1
    have hmax := pathWeight_le_lastPassage ω p
    linarith
  · obtain ⟨p, hp⟩ := exists_pathWeight_eq_lastPassage ω 0 d
    have hb := (abs_le.mp (abs_pathWeight_sub_le_two_mul hω hη k h p)).2
    have hmax := pathWeight_le_lastPassage η p
    linarith

end LPPDifferentiability
