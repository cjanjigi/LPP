/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Paths.Geometry
public import LPP_Foundations.Model.LastPassage.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Passage weights depend only on the rectangle between their endpoints. -/

@[expose] public section

namespace LPPDifferentiability

/-- Equality of environments on the endpoint rectangle gives equality of path weights. -/
theorem pathWeight_eq_of_eqOn {ω η : Environment} {u : Lattice} {d : ℕ × ℕ}
    (h : Set.EqOn ω η (Set.Icc u (u + ((d.1 : ℤ), (d.2 : ℤ)))))
    (p : Path u d) : pathWeight ω p = pathWeight η p := by
  apply Finset.sum_congr rfl
  intro i _
  exact h (p.vertex_mem_Icc i.castSucc)

/-- A pointwise inequality on the endpoint rectangle compares path weights. -/
theorem pathWeight_le_of_leOn {ω η : Environment} {u : Lattice} {d : ℕ × ℕ}
    (h : ∀ x ∈ Set.Icc u (u + ((d.1 : ℤ), (d.2 : ℤ))), ω x ≤ η x)
    (p : Path u d) : pathWeight ω p ≤ pathWeight η p := by
  apply Finset.sum_le_sum
  intro i _
  exact h _ (p.vertex_mem_Icc i.castSucc)

/-- A pointwise inequality on the endpoint rectangle compares last-passage times. -/
theorem lastPassage_le_of_leOn {ω η : Environment} {u : Lattice} {d : ℕ × ℕ}
    (h : ∀ x ∈ Set.Icc u (u + ((d.1 : ℤ), (d.2 : ℤ))), ω x ≤ η x) :
    lastPassage ω u d ≤ lastPassage η u d := by
  obtain ⟨p, hp⟩ := exists_pathWeight_eq_lastPassage ω u d
  rw [← hp]
  exact (pathWeight_le_of_leOn h p).trans (pathWeight_le_lastPassage η p)

/-- Equality on the endpoint rectangle gives equality of the finite maxima. -/
theorem lastPassage_eq_of_eqOn {ω η : Environment} {u : Lattice} {d : ℕ × ℕ}
    (h : Set.EqOn ω η (Set.Icc u (u + ((d.1 : ℤ), (d.2 : ℤ))))) :
    lastPassage ω u d = lastPassage η u d := by
  apply le_antisymm
  · exact lastPassage_le_of_leOn (fun x hx => le_of_eq (h hx))
  · exact lastPassage_le_of_leOn (fun x hx => le_of_eq (h hx).symm)

end LPPDifferentiability
