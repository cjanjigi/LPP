/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.Lattice

/-! The southeast order compares the two outgoing edge increments at every lattice site. -/

@[expose] public section

open LPPDifferentiability

namespace LPP.Busemann

/-- At every site, `B` has an east increment at least as large as `C` and a north
increment at most as large as `C`. This is the southeast order on cocycles
in Strong Existence, Section 2.2. -/
def cocycleSoutheastLE (B C : Lattice → Lattice → ℝ) : Prop :=
  ∀ x : Lattice,
    C x (x + ((1 : ℤ), (0 : ℤ))) ≤ B x (x + ((1 : ℤ), (0 : ℤ))) ∧
    B x (x + ((0 : ℤ), (1 : ℤ))) ≤ C x (x + ((0 : ℤ), (1 : ℤ)))

/-- Expand the southeast order into the two inequalities at every site. -/
theorem cocycleSoutheastLE_iff (B C : Lattice → Lattice → ℝ) :
    cocycleSoutheastLE B C ↔
      ∀ x : Lattice,
        C x (x + ((1 : ℤ), (0 : ℤ))) ≤ B x (x + ((1 : ℤ), (0 : ℤ))) ∧
        B x (x + ((0 : ℤ), (1 : ℤ))) ≤ C x (x + ((0 : ℤ), (1 : ℤ))) :=
  Iff.rfl

/-- Every cocycle lies below itself in the southeast order. -/
theorem cocycleSoutheastLE_refl (B : Lattice → Lattice → ℝ) :
    cocycleSoutheastLE B B :=
  fun _ => ⟨le_rfl, le_rfl⟩

/-- Southeast comparisons compose in the same direction. -/
theorem cocycleSoutheastLE_trans {B C D : Lattice → Lattice → ℝ}
    (hBC : cocycleSoutheastLE B C) (hCD : cocycleSoutheastLE C D) :
    cocycleSoutheastLE B D :=
  fun x => ⟨le_trans (hCD x).1 (hBC x).1, le_trans (hBC x).2 (hCD x).2⟩

end LPP.Busemann
