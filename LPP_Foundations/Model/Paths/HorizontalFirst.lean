/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.Path
public import Lean.Elab.Tactic.Omega

/-! # The horizontal-first path

For a lattice point `u` and a displacement `d = (d₁, d₂)`, `horizontalFirst u d` is the admissible
path from `u` to `u + d` that takes its first `d₁` steps in the first coordinate and then its `d₂`
steps in the second coordinate.
-/

@[expose] public section

namespace LPPDifferentiability

def horizontalFirst (u : Lattice) (d : ℕ × ℕ) : Path u d where
  vertex i := (u.1 + (min i.val d.1 : ℕ), u.2 + (i.val - d.1 : ℕ))
  start := by simp
  finish := by
    apply Prod.ext <;> simp
  step i := by
    by_cases h : i.val < d.1
    · left
      apply Prod.ext
      · simp only [Fin.val_succ, Fin.val_castSucc, Prod.fst_add]
        rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]
        simp only [Nat.cast_add, Nat.cast_one]
        omega
      · simp only [Fin.val_succ, Fin.val_castSucc, Prod.snd_add]
        rw [Nat.sub_eq_zero_of_le (by omega), Nat.sub_eq_zero_of_le (by omega)]
        simp
    · right
      apply Prod.ext
      · simp only [Fin.val_succ, Fin.val_castSucc, Prod.fst_add]
        rw [Nat.min_eq_right (by omega), Nat.min_eq_right (by omega)]
        simp
      · simp only [Fin.val_succ, Fin.val_castSucc, Prod.snd_add]
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
        simp only [Nat.cast_add, Nat.cast_one]
        omega

end LPPDifferentiability
