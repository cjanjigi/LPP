/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.LastPassage.Basic
public import LPP_Foundations.Model.Paths.Swap

/-! Deterministic covariance of signed passage maxima under coordinate transposition. -/

@[expose] public section

namespace LPPDifferentiability

/-- Swapping endpoints and the site field preserves the finite maximum, with no
sign or moment assumptions on the field. -/
theorem lastPassage_swap (ω : Environment) (u : Lattice) (d : ℕ × ℕ) :
    lastPassage ω u.swap d.swap = lastPassage (fun z => ω z.swap) u d := by
  apply le_antisymm
  · obtain ⟨p, hp⟩ := exists_pathWeight_eq_lastPassage ω u.swap d.swap
    calc
      lastPassage ω u.swap d.swap = pathWeight ω p := hp.symm
      _ = pathWeight (fun z => ω z.swap) p.swap := by
        calc
          pathWeight ω p = pathWeight ω p.swap.swap := by rw [Path.swap_swap]
          _ = pathWeight (fun z => ω z.swap) p.swap := pathWeight_swap ω p.swap
      _ ≤ lastPassage (fun z => ω z.swap) u d :=
        pathWeight_le_lastPassage (fun z => ω z.swap) p.swap
  · obtain ⟨p, hp⟩ := exists_pathWeight_eq_lastPassage (fun z => ω z.swap) u d
    calc
      lastPassage (fun z => ω z.swap) u d = pathWeight (fun z => ω z.swap) p := hp.symm
      _ = pathWeight ω p.swap := (pathWeight_swap ω p).symm
      _ ≤ lastPassage ω u.swap d.swap := pathWeight_le_lastPassage ω p.swap

end LPPDifferentiability
