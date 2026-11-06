/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.Lattice
public import Mathlib.Data.Int.Interval
public import Mathlib.Basic.Finite.Defs
public import Mathlib.SetTheory.Cardinal.Finite

import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! # Counting planar coarse-center sequences

The finite family counted here is the center sequence used in the planar
coarse covering argument: it starts at the origin and each coordinate changes
by at most one at every step.
-/

@[expose] public section

namespace LPPDifferentiability

/-- The family of planar center sequences of length `r` steps. -/
def centerSequenceFamily (r : ℕ) : Set (Fin (r + 1) → Lattice) :=
  {u | u 0 = 0 ∧
    ∀ i : Fin r,
      |(u i.succ).1 - (u i.castSucc).1| ≤ 1 ∧
      |(u i.succ).2 - (u i.castSucc).2| ≤ 1}

/-- Membership in `centerSequenceFamily` is exactly the condition on the steps. -/
theorem mem_centerSequenceFamily_iff (r : ℕ) (u : Fin (r + 1) → Lattice) :
    u ∈ centerSequenceFamily r ↔
      u 0 = 0 ∧
      ∀ i : Fin r,
        |(u i.succ).1 - (u i.castSucc).1| ≤ 1 ∧
        |(u i.succ).2 - (u i.castSucc).2| ≤ 1 := Iff.rfl

/-- The nine possible coordinatewise increments of one planar center step. -/
abbrev CenterIncrementAlphabet : Type :=
  Set.Icc (-1 : ℤ) 1 × Set.Icc (-1 : ℤ) 1

/-- Record the increment at every step of a center sequence. -/
def centerSequenceIncrements (r : ℕ) (u : centerSequenceFamily r) :
    Fin r → CenterIncrementAlphabet :=
  fun i =>
    let hstep := u.property.2 i
    let hx := abs_le.mp hstep.1
    let hy := abs_le.mp hstep.2
    (⟨(u.1 i.succ).1 - (u.1 i.castSucc).1, hx.1, hx.2⟩,
      ⟨(u.1 i.succ).2 - (u.1 i.castSucc).2, hy.1, hy.2⟩)

/-- Equal increment records determine the center sequence, starting from its
fixed initial value. -/
theorem centerSequenceIncrements_injective (r : ℕ) :
    Function.Injective (centerSequenceIncrements r) := by
  intro u v huv
  apply Subtype.ext
  funext i
  induction i using Fin.induction with
  | zero =>
      exact u.property.1.trans v.property.1.symm
  | succ j ih =>
      have hcode := congrFun huv j
      dsimp [centerSequenceIncrements] at hcode
      have hx :
          (u.1 j.succ).1 - (u.1 j.castSucc).1 =
            (v.1 j.succ).1 - (v.1 j.castSucc).1 :=
        congrArg Subtype.val (congrArg Prod.fst hcode)
      have hy :
          (u.1 j.succ).2 - (u.1 j.castSucc).2 =
            (v.1 j.succ).2 - (v.1 j.castSucc).2 :=
        congrArg Subtype.val (congrArg Prod.snd hcode)
      apply Prod.ext
      · have hprev := congrArg Prod.fst ih
        omega
      · have hprev := congrArg Prod.snd ih
        omega

/-- The planar center-sequence family is finite. -/
theorem finite_centerSequenceFamily (r : ℕ) :
    Finite (centerSequenceFamily r) := by
  classical
  exact Finite.of_injective (centerSequenceIncrements r)
    (centerSequenceIncrements_injective r)

/-- The family has at most `9^r` center sequences, including the case `r = 0`. -/
theorem natCard_centerSequenceFamily_le (r : ℕ) :
    Nat.card (centerSequenceFamily r) ≤ 9 ^ r := by
  classical
  calc
    Nat.card (centerSequenceFamily r) ≤
        Nat.card (Fin r → CenterIncrementAlphabet) :=
      Nat.card_le_card_of_injective (centerSequenceIncrements r)
        (centerSequenceIncrements_injective r)
    _ = Nat.card CenterIncrementAlphabet ^ Nat.card (Fin r) := Nat.card_fun
    _ = 9 ^ r := by
      rw [Nat.card_fin]
      have hinterval : Nat.card (Set.Icc (-1 : ℤ) 1) = 3 := by
        have hcast :
            (Fintype.card (Set.Icc (-1 : ℤ) 1) : ℤ) = 3 := by
          rw [Fintype.card_Icc]
          rw [Int.card_Icc_of_le (a := -1) (b := 1) (by omega)]
          norm_num
        rw [Nat.card_eq_fintype_card]
        exact_mod_cast hcast
      rw [CenterIncrementAlphabet, Nat.card_prod, hinterval]

end LPPDifferentiability
