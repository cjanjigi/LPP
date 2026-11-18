/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.Lattice
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Order.Basic
import Lean.Elab.Tactic.Omega

/-! The natural displacement between coordinatewise ordered lattice sites. -/

@[expose] public section

namespace LPPDifferentiability

/-- The two coordinate differences from `a` to `b` as natural numbers. This is
the displacement of an up-right path when `a ≤ b`. -/
def natDisplacement (a b : Lattice) : ℕ × ℕ :=
  ((b.1 - a.1).toNat, (b.2 - a.2).toNat)

/-- Adding the displacement to the lower site recovers the upper site. -/
theorem add_cast_natDisplacement (a b : Lattice) (h : a ≤ b) :
    a + (((natDisplacement a b).1 : ℤ), ((natDisplacement a b).2 : ℤ)) = b := by
  have h1 := Int.toNat_of_nonneg (show 0 ≤ b.1 - a.1 by have := h.1; omega)
  have h2 := Int.toNat_of_nonneg (show 0 ≤ b.2 - a.2 by have := h.2; omega)
  apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, natDisplacement] <;> omega

/-- Displacements add along a coordinatewise nondecreasing triple of sites. -/
theorem natDisplacement_add (a b c : Lattice) (hab : a ≤ b) (hbc : b ≤ c) :
    natDisplacement a b + natDisplacement b c = natDisplacement a c := by
  have hab₁ := congrArg Prod.fst (add_cast_natDisplacement a b hab)
  have hab₂ := congrArg Prod.snd (add_cast_natDisplacement a b hab)
  have hbc₁ := congrArg Prod.fst (add_cast_natDisplacement b c hbc)
  have hbc₂ := congrArg Prod.snd (add_cast_natDisplacement b c hbc)
  have hac₁ := congrArg Prod.fst (add_cast_natDisplacement a c (le_trans hab hbc))
  have hac₂ := congrArg Prod.snd (add_cast_natDisplacement a c (le_trans hab hbc))
  simp only [Prod.fst_add, Prod.snd_add] at hab₁ hab₂ hbc₁ hbc₂ hac₁ hac₂
  apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add] <;>
    apply Int.ofNat_inj.mp <;> simp only [← Int.ofNat_add_ofNat] <;> omega

/-- The unique natural displacement taking `a` to `b`. -/
theorem natDisplacement_unique (a b : Lattice) (d : ℕ × ℕ)
    (h : a + ((d.1 : ℤ), (d.2 : ℤ)) = b) (hab : a ≤ b) :
    d = natDisplacement a b := by
  have h' := add_cast_natDisplacement a b hab
  have h1 := congrArg Prod.fst (h.trans h'.symm)
  have h2 := congrArg Prod.snd (h.trans h'.symm)
  simp only [Prod.fst_add, Prod.snd_add] at h1 h2
  apply Prod.ext <;> omega

end LPPDifferentiability
