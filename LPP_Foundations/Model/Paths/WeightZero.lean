/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.PathWeight

/-! # The weight of a path with zero displacement

A path with displacement `(0, 0)` is the trivial path, and its weight is zero.
-/

@[expose] public section

namespace LPPDifferentiability

theorem pathWeight_zero (ω : Environment) (u : Lattice) (p : Path u (0, 0)) :
    pathWeight ω p = 0 := by
  simp [pathWeight]

end LPPDifferentiability
