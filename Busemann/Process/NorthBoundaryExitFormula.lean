/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Process.NorthBoundaryExitUpper
public import Busemann.Process.NorthBoundaryExitLower

/-! Assemble the two inequalities into the finite north-boundary exit formula. -/

@[expose] public section

open LPP.Busemann LPPDifferentiability

namespace LPP.Busemann

/-- The last-passage value with only the north boundary changed is the maximum
over all horizontal exit locations. This derived one-sided formula uses the
exit decomposition of GRS 1510.00859v2, Lemma 6.4; its two-boundary NE
passage is defined in (6.8). -/
theorem north_boundary_passage_eq_exit_sup
    (ω : Environment) (C : Lattice → Lattice → ℝ)
    (hC : is_additive C) (hrec : recovers_environment ω C)
    (x : Lattice) (d : ℕ × ℕ) :
    let v : Lattice := x + ((d.1 : ℤ), (d.2 : ℤ))
    let N : Environment := fun z =>
      if z.2 = v.2 ∧ z.1 < v.1 then C z (z + (1, 0)) else ω z
    lastPassage N x d =
      (Finset.univ : Finset (Fin (d.1 + 1))).sup' Finset.univ_nonempty
        (fun k => lastPassage ω x (d.1 - k.val, d.2) +
          C (v - ((k.val : ℤ), 0)) v) := by
  let v : Lattice := x + ((d.1 : ℤ), (d.2 : ℤ))
  let N : Environment := fun z =>
    if z.2 = v.2 ∧ z.1 < v.1 then C z (z + (1, 0)) else ω z
  change lastPassage N x d =
    (Finset.univ : Finset (Fin (d.1 + 1))).sup' Finset.univ_nonempty
      (fun k => lastPassage ω x (d.1 - k.val, d.2) +
        C (v - ((k.val : ℤ), 0)) v)
  apply le_antisymm
  · obtain ⟨p, hp⟩ := exists_pathWeight_eq_lastPassage N x d
    calc
      lastPassage N x d = pathWeight N p := hp.symm
      _ ≤ (Finset.univ : Finset (Fin (d.1 + 1))).sup' Finset.univ_nonempty
          (fun k => lastPassage ω x (d.1 - k.val, d.2) +
            C (v - ((k.val : ℤ), 0)) v) :=
        north_boundary_pathWeight_le_exit_max ω C hC x d p
  · exact north_boundary_exit_max_le_lastPassage ω C hC hrec x d

end LPP.Busemann
