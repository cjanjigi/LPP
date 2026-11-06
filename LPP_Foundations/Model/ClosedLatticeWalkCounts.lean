/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.Lattice
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Lean.Elab.Tactic.Omega

/-! Direction counts for closed signed lattice walks. -/

@[expose] public section

namespace LPPDifferentiability

/-- A closed nearest-neighbor walk has equal opposite-direction counts. -/
theorem closed_lattice_walk_direction_balance
    (m : ℕ) (v : Fin (m + 1) → Lattice)
    (hclosed : v (0 : Fin (m + 1)) = v (Fin.last m))
    (hstep : ∀ i : Fin m,
      v i.succ - v i.castSucc = (0, 1) ∨
      v i.succ - v i.castSucc = (0, -1) ∨
      v i.succ - v i.castSucc = (-1, 0) ∨
      v i.succ - v i.castSucc = (1, 0)) :
    let U : Finset (Fin m) := Finset.univ.filter
      (fun i => v i.succ - v i.castSucc = (0, 1))
    let D : Finset (Fin m) := Finset.univ.filter
      (fun i => v i.succ - v i.castSucc = (0, -1))
    let L : Finset (Fin m) := Finset.univ.filter
      (fun i => v i.succ - v i.castSucc = (-1, 0))
    let R : Finset (Fin m) := Finset.univ.filter
      (fun i => v i.succ - v i.castSucc = (1, 0))
    U.card = D.card ∧ L.card = R.card ∧ 2 * (U.card + L.card) = m := by
  classical
  dsimp only
  let U : Finset (Fin m) := Finset.univ.filter
    (fun i => v i.succ - v i.castSucc = (0, 1))
  let D : Finset (Fin m) := Finset.univ.filter
    (fun i => v i.succ - v i.castSucc = (0, -1))
  let L : Finset (Fin m) := Finset.univ.filter
    (fun i => v i.succ - v i.castSucc = (-1, 0))
  let R : Finset (Fin m) := Finset.univ.filter
    (fun i => v i.succ - v i.castSucc = (1, 0))
  change U.card = D.card ∧ L.card = R.card ∧ 2 * (U.card + L.card) = m
  have hXstep (i : Fin m) :
      (if v i.succ - v i.castSucc = (1, 0) then (1 : ℤ) else 0) -
        (if v i.succ - v i.castSucc = (-1, 0) then 1 else 0) =
        (v i.succ).1 - (v i.castSucc).1 := by
    rcases hstep i with hu | hd | hl | hr
    · have hcoord : (v i.succ).1 - (v i.castSucc).1 = 0 := by
        simpa using congrArg Prod.fst hu
      simpa [hu] using hcoord.symm
    · have hcoord : (v i.succ).1 - (v i.castSucc).1 = 0 := by
        simpa using congrArg Prod.fst hd
      simpa [hd] using hcoord.symm
    · have hcoord : (v i.succ).1 - (v i.castSucc).1 = -1 := by
        simpa using congrArg Prod.fst hl
      simpa [hl] using hcoord.symm
    · have hcoord : (v i.succ).1 - (v i.castSucc).1 = 1 := by
        simpa using congrArg Prod.fst hr
      simpa [hr] using hcoord.symm
  have hYstep (i : Fin m) :
      (if v i.succ - v i.castSucc = (0, 1) then (1 : ℤ) else 0) -
        (if v i.succ - v i.castSucc = (0, -1) then 1 else 0) =
        (v i.succ).2 - (v i.castSucc).2 := by
    rcases hstep i with hu | hd | hl | hr
    · have hcoord : (v i.succ).2 - (v i.castSucc).2 = 1 := by
        simpa using congrArg Prod.snd hu
      simpa [hu] using hcoord.symm
    · have hcoord : (v i.succ).2 - (v i.castSucc).2 = -1 := by
        simpa using congrArg Prod.snd hd
      simpa [hd] using hcoord.symm
    · have hcoord : (v i.succ).2 - (v i.castSucc).2 = 0 := by
        simpa using congrArg Prod.snd hl
      simpa [hl] using hcoord.symm
    · have hcoord : (v i.succ).2 - (v i.castSucc).2 = 0 := by
        simpa using congrArg Prod.snd hr
      simpa [hr] using hcoord.symm
  have hUcard : (U.card : ℤ) =
      ∑ i ∈ (Finset.univ : Finset (Fin m)),
        if v i.succ - v i.castSucc = (0, 1) then (1 : ℤ) else 0 := by
    change ((Finset.univ.filter (fun i : Fin m =>
      v i.succ - v i.castSucc = (0, 1))).card : ℤ) = _
    rw [Finset.natCast_card_filter]
  have hDcard : (D.card : ℤ) =
      ∑ i ∈ (Finset.univ : Finset (Fin m)),
        if v i.succ - v i.castSucc = (0, -1) then (1 : ℤ) else 0 := by
    change ((Finset.univ.filter (fun i : Fin m =>
      v i.succ - v i.castSucc = (0, -1))).card : ℤ) = _
    rw [Finset.natCast_card_filter]
  have hLcard : (L.card : ℤ) =
      ∑ i ∈ (Finset.univ : Finset (Fin m)),
        if v i.succ - v i.castSucc = (-1, 0) then (1 : ℤ) else 0 := by
    change ((Finset.univ.filter (fun i : Fin m =>
      v i.succ - v i.castSucc = (-1, 0))).card : ℤ) = _
    rw [Finset.natCast_card_filter]
  have hRcard : (R.card : ℤ) =
      ∑ i ∈ (Finset.univ : Finset (Fin m)),
        if v i.succ - v i.castSucc = (1, 0) then (1 : ℤ) else 0 := by
    change ((Finset.univ.filter (fun i : Fin m =>
      v i.succ - v i.castSucc = (1, 0))).card : ℤ) = _
    rw [Finset.natCast_card_filter]
  have hYcount : (U.card : ℤ) - D.card =
      ∑ i : Fin m, ((v i.succ).2 - (v i.castSucc).2) := by
    rw [hUcard, hDcard, ← Finset.sum_sub_distrib]
    simp_rw [hYstep]
  have hXcount : (R.card : ℤ) - L.card =
      ∑ i : Fin m, ((v i.succ).1 - (v i.castSucc).1) := by
    rw [hRcard, hLcard, ← Finset.sum_sub_distrib]
    simp_rw [hXstep]
  have hclosedX := congrArg Prod.fst hclosed
  have hclosedY := congrArg Prod.snd hclosed
  have hYsucc_cast :
      (∑ i : Fin m, (v i.succ).2) = ∑ i : Fin m, (v i.castSucc).2 := by
    have hsum := Fin.sum_univ_succ (fun i : Fin (m + 1) => (v i).2)
    have hsum' := Fin.sum_univ_castSucc (fun i : Fin (m + 1) => (v i).2)
    rw [← hclosedY] at hsum'
    omega
  have hXsucc_cast :
      (∑ i : Fin m, (v i.succ).1) = ∑ i : Fin m, (v i.castSucc).1 := by
    have hsum := Fin.sum_univ_succ (fun i : Fin (m + 1) => (v i).1)
    have hsum' := Fin.sum_univ_castSucc (fun i : Fin (m + 1) => (v i).1)
    rw [← hclosedX] at hsum'
    omega
  have hYzero :
      (∑ i : Fin m, ((v i.succ).2 - (v i.castSucc).2)) = 0 := by
    rw [Finset.sum_sub_distrib, hYsucc_cast, sub_self]
  have hXzero :
      (∑ i : Fin m, ((v i.succ).1 - (v i.castSucc).1)) = 0 := by
    rw [Finset.sum_sub_distrib, hXsucc_cast, sub_self]
  have hUD : U.card = D.card := by
    have hbalance : (U.card : ℤ) - D.card = 0 := by
      rw [hYcount, hYzero]
    exact_mod_cast (sub_eq_zero.mp hbalance)
  have hLR : L.card = R.card := by
    have hbalance : (R.card : ℤ) - L.card = 0 := by
      rw [hXcount, hXzero]
    have hcast : (R.card : ℤ) = (L.card : ℤ) := sub_eq_zero.mp hbalance
    exact_mod_cast hcast.symm
  have hclass (i : Fin m) :
      (if v i.succ - v i.castSucc = (0, 1) then (1 : ℤ) else 0) +
      (if v i.succ - v i.castSucc = (0, -1) then 1 else 0) +
      (if v i.succ - v i.castSucc = (-1, 0) then 1 else 0) +
      (if v i.succ - v i.castSucc = (1, 0) then 1 else 0) = 1 := by
    rcases hstep i with hu | hd | hl | hr
    · simp [hu]
    · simp [hd]
    · simp [hl]
    · simp [hr]
  have htotal :
      (U.card : ℤ) + D.card + L.card + R.card = m := by
    rw [hUcard, hDcard, hLcard, hRcard]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    calc
      ∑ i ∈ (Finset.univ : Finset (Fin m)),
          ((if v i.succ - v i.castSucc = (0, 1) then (1 : ℤ) else 0) +
          (if v i.succ - v i.castSucc = (0, -1) then 1 else 0) +
          (if v i.succ - v i.castSucc = (-1, 0) then 1 else 0) +
          (if v i.succ - v i.castSucc = (1, 0) then 1 else 0)) =
        ∑ i ∈ (Finset.univ : Finset (Fin m)), (1 : ℤ) := by
          apply Finset.sum_congr rfl
          intro i _
          exact hclass i
      _ = m := by simp
  have htotalNat : U.card + D.card + L.card + R.card = m := by
    exact_mod_cast htotal
  exact ⟨hUD, hLR, by omega⟩

end LPPDifferentiability
