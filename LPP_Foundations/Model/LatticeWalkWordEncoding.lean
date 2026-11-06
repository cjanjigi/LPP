/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.Lattice
public import Mathlib.Data.List.ChainOfFn
import Mathlib.Algebra.Group.Prod
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! Direction lists for actual unit lattice walks with a fixed starting vertex. -/

@[expose] public section

namespace LPPDifferentiability

private theorem exists_direction_of_unit_step (a b : Lattice)
    (h : b - a = (0, 1) ∨ b - a = (0, -1) ∨
      b - a = (-1, 0) ∨ b - a = (1, 0)) :
    ∃ d : Fin 4, (d = 0 ∧ b - a = (1, 0)) ∨
      (d = 1 ∧ b - a = (0, 1)) ∨
      (d = 2 ∧ b - a = (-1, 0)) ∨ (d = 3 ∧ b - a = (0, -1)) := by
  rcases h with h | h | h | h
  · exact ⟨1, Or.inr (Or.inl ⟨rfl, h⟩)⟩
  · exact ⟨3, Or.inr (Or.inr (Or.inr ⟨rfl, h⟩))⟩
  · exact ⟨2, Or.inr (Or.inr (Or.inl ⟨rfl, h⟩))⟩
  · exact ⟨0, Or.inl ⟨rfl, h⟩⟩

/-- Actual fixed-start unit walks admit injective chronological direction lists.
The labels are right, up, left, down in that order. Only immediate reversal
is excluded by the final implication; longer returns and open walks are allowed. -/
theorem exists_injective_lattice_walk_direction_lists (x : Lattice) (m : ℕ) :
    ∃ encode : {v : Fin (m + 1) → Lattice // v 0 = x ∧
        ∀ i : Fin m, v i.succ - v i.castSucc = (0, 1) ∨
          v i.succ - v i.castSucc = (0, -1) ∨
          v i.succ - v i.castSucc = (-1, 0) ∨
          v i.succ - v i.castSucc = (1, 0)} → List (Fin 4),
      Function.Injective encode ∧ ∀ v,
        (encode v).length = m ∧
        (∃ d : Fin m → Fin 4, encode v = List.ofFn d ∧
          ∀ i, (d i = 0 ∧ v.val i.succ - v.val i.castSucc = (1, 0)) ∨
            (d i = 1 ∧ v.val i.succ - v.val i.castSucc = (0, 1)) ∨
            (d i = 2 ∧ v.val i.succ - v.val i.castSucc = (-1, 0)) ∨
            (d i = 3 ∧ v.val i.succ - v.val i.castSucc = (0, -1))) ∧
        ((∀ (i : ℕ) (hi : i + 2 ≤ m),
          v.val ⟨i + 2, by omega⟩ ≠ v.val ⟨i, by omega⟩) →
          (encode v).IsChain (fun a b : Fin 4 => b ≠ a + 2)) := by
  classical
  let W := {v : Fin (m + 1) → Lattice // v 0 = x ∧
    ∀ i : Fin m, v i.succ - v i.castSucc = (0, 1) ∨
      v i.succ - v i.castSucc = (0, -1) ∨
      v i.succ - v i.castSucc = (-1, 0) ∨
      v i.succ - v i.castSucc = (1, 0)}
  have hex (v : W) (i : Fin m) :=
    exists_direction_of_unit_step (v.val i.castSucc) (v.val i.succ) (v.property.2 i)
  choose d hd using hex
  have hdecode (v : W) (i : Fin m) :
      v.val i.succ - v.val i.castSucc =
        (if d v i = 0 then (1, 0) else if d v i = 1 then (0, 1)
          else if d v i = 2 then (-1, 0) else (0, -1)) := by
    rcases hd v i with ⟨h, hs⟩ | ⟨h, hs⟩ | ⟨h, hs⟩ | ⟨h, hs⟩ <;>
      norm_num [h, hs]
  refine ⟨fun v => List.ofFn (d v), ?_, ?_⟩
  · intro v w he
    have he' := List.ofFn_injective he
    apply Subtype.ext
    funext i
    induction i using Fin.induction with
    | zero => exact v.property.1.trans w.property.1.symm
    | succ i ih =>
      have hs : v.val i.succ - v.val i.castSucc =
          w.val i.succ - w.val i.castSucc := by
        rw [hdecode, hdecode, congrFun he' i]
      rw [ih] at hs
      exact sub_left_inj.mp hs
  · intro v
    refine ⟨List.length_ofFn, ⟨d v, rfl, hd v⟩, ?_⟩
    intro hback
    apply List.isChain_ofFn.mpr
    intro i hi he
    have ha := hd v ⟨i, by omega⟩
    have hb := hd v ⟨i + 1, hi⟩
    have hs : v.val (⟨i + 1, hi⟩ : Fin m).succ -
        v.val (⟨i + 1, hi⟩ : Fin m).castSucc =
        -(v.val (⟨i, by omega⟩ : Fin m).succ -
          v.val (⟨i, by omega⟩ : Fin m).castSucc) := by
      rcases ha with ⟨ha, hsa⟩ | ⟨ha, hsa⟩ | ⟨ha, hsa⟩ | ⟨ha, hsa⟩ <;>
        rcases hb with ⟨hb, hsb⟩ | ⟨hb, hsb⟩ | ⟨hb, hsb⟩ | ⟨hb, hsb⟩ <;>
        norm_num [ha, hb] at he <;>
        rw [hsa, hsb] <;> decide
    apply hback i (by omega)
    change v.val ⟨i + 2, by omega⟩ - v.val ⟨i + 1, by omega⟩ =
      -(v.val ⟨i + 1, by omega⟩ - v.val ⟨i, by omega⟩) at hs
    rw [neg_sub] at hs
    exact sub_left_inj.mp hs

end LPPDifferentiability
