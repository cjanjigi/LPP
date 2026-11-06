/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Paths.HorizontalFirst

/-! # Nonempty spaces of paths

For every `u` and `d`, the space of paths from `u` with displacement `d` is nonempty, since it
contains `horizontalFirst u d`.
-/

@[expose] public section

namespace LPPDifferentiability

instance pathNonempty (u : Lattice) (d : ℕ × ℕ) : Nonempty (Path u d) :=
  ⟨horizontalFirst u d⟩

end LPPDifferentiability
