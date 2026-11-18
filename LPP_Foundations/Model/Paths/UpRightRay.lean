/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.Lattice
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Order.Monotone.Basic
import Lean.Elab.Tactic.Omega

/-! Up-right lattice rays and their signed absolute levels. -/

@[expose] public section

namespace LPPDifferentiability

/-- A lattice ray is up-right if every step is one unit east or north. -/
def IsUpRightRay (γ : ℕ → Lattice) : Prop :=
  ∀ n : ℕ, γ (n + 1) = γ n + (1, 0) ∨ γ (n + 1) = γ n + (0, 1)

/-- An up-right ray is nondecreasing in each coordinate. -/
theorem IsUpRightRay.monotone {γ : ℕ → Lattice} (hγ : IsUpRightRay γ) : Monotone γ := by
  apply monotone_nat_of_le_succ
  intro n
  rcases hγ n with he | hn
  · rw [he]
    constructor <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega
  · rw [hn]
    constructor <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega

/-- The signed absolute level increases by one at every step of the ray. -/
theorem IsUpRightRay.level {γ : ℕ → Lattice} (hγ : IsUpRightRay γ) (n : ℕ) :
    (γ n).1 + (γ n).2 = (γ 0).1 + (γ 0).2 + (n : ℤ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rcases hγ n with he | hn
      · rw [he]
        simp only [Prod.fst_add, Prod.snd_add, Nat.cast_succ]
        omega
      · rw [hn]
        simp only [Prod.fst_add, Prod.snd_add, Nat.cast_succ]
        omega

end LPPDifferentiability
