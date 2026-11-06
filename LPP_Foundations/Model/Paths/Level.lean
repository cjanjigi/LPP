/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.Path
public import Lean.Elab.Tactic.Omega

/-! # The level of a path

Each step of an admissible path raises the level `z₁ + z₂` by one. `Path.level` records this: the
vertex with index `i` of a path from `u` lies on level `u₁ + u₂ + i`.
-/

@[expose] public section

namespace LPPDifferentiability

theorem Path.level {u : Lattice} {d : ℕ × ℕ} (p : Path u d)
    (i : Fin (d.1 + d.2 + 1)) :
    (p.vertex i).1 + (p.vertex i).2 = u.1 + u.2 + (i.val : ℤ) := by
  induction i using Fin.induction with
  | zero => simp [p.start]
  | succ j ih =>
    simp only [Fin.val_castSucc] at ih
    rcases p.step j with h | h
    · have h₁ := congrArg Prod.fst h
      have h₂ := congrArg Prod.snd h
      simp only [Prod.fst_add, Prod.snd_add] at h₁ h₂
      simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
      omega
    · have h₁ := congrArg Prod.fst h
      have h₂ := congrArg Prod.snd h
      simp only [Prod.fst_add, Prod.snd_add] at h₁ h₂
      simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
      omega

end LPPDifferentiability
