/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.Path

/-! # The step code of a path

The step code of a path records, for each step, whether the step is `(1, 0)` (true) or `(0, 1)`
(false). `stepCode p` is this sequence of booleans.
-/

@[expose] public section

namespace LPPDifferentiability

noncomputable def stepCode {u : Lattice} {d : ℕ × ℕ} (p : Path u d) :
    Fin (d.1 + d.2) → Bool := fun i =>
  decide (p.vertex i.succ = p.vertex i.castSucc + (1, 0))

end LPPDifferentiability
