/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.FiniteWordsForbiddenSuccessor
public import LPP_Foundations.Model.LatticeWalkWordEncoding
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega

/-! Finite sets of unit walks without immediate returns.
These sets include open walks and need not consist of circuits. -/
public section

namespace LPPDifferentiability

/-- Walks from a fixed start have the four-times-three upper bound.
The ambient lattice-function type is infinite; its finiteness is not assumed. -/
theorem exists_finset_nonbacktracking_walks (x : Lattice) (m : ℕ) (hm : 0 < m) :
    ∃ W : Finset (Fin (m + 1) → Lattice),
      (∀ v, v ∈ W ↔ v 0 = x ∧
        (∀ i : Fin m, v i.succ - v i.castSucc = (0, 1) ∨
          v i.succ - v i.castSucc = (0, -1) ∨
          v i.succ - v i.castSucc = (-1, 0) ∨
          v i.succ - v i.castSucc = (1, 0)) ∧
        (∀ (i : ℕ) (hi : i + 2 ≤ m),
          v ⟨i + 2, by omega⟩ ≠ v ⟨i, by omega⟩)) ∧
      W.card ≤ 4 * 3 ^ (m - 1) := by
  classical
  obtain ⟨D, hD, hcard⟩ := exists_finset_four_direction_words (m - 1)
  obtain ⟨encode, hinj, hencode⟩ :=
    exists_injective_lattice_walk_direction_lists x m
  let S : Set (Fin (m + 1) → Lattice) := {v | v 0 = x ∧
    (∀ i : Fin m, v i.succ - v i.castSucc = (0, 1) ∨
      v i.succ - v i.castSucc = (0, -1) ∨
      v i.succ - v i.castSucc = (-1, 0) ∨
      v i.succ - v i.castSucc = (1, 0)) ∧
    (∀ (i : ℕ) (hi : i + 2 ≤ m),
      v ⟨i + 2, by omega⟩ ≠ v ⟨i, by omega⟩)}
  let f : S → {w // w ∈ D} := fun v =>
    ⟨encode ⟨v.val, v.property.1, v.property.2.1⟩, (hD _).mpr
      ⟨by rw [(hencode _).1]; omega,
        (hencode _).2.2 v.property.2.2⟩⟩
  have hf : Function.Injective f := by
    intro v w h
    apply Subtype.ext
    exact Subtype.mk.inj (hinj (congrArg Subtype.val h))
  let : Finite S := Finite.of_injective f hf
  let : Fintype S := Fintype.ofFinite S
  refine ⟨S.toFinset, fun v => Set.mem_toFinset, ?_⟩
  rw [Set.toFinset_card]
  calc
    Fintype.card S ≤ Fintype.card {w // w ∈ D} := Fintype.card_le_of_injective f hf
    _ = D.card := Fintype.card_coe D
    _ = 4 * 3 ^ (m - 1) := hcard

/-- A finite collection of possible starts contributes its cardinality as a factor.
Membership describes all such walks, including any open walks. -/
theorem exists_finset_nonbacktracking_walks_from (B : Finset Lattice)
    (m : ℕ) (hm : 0 < m) :
    ∃ W : Finset (Fin (m + 1) → Lattice),
      (∀ v, v ∈ W ↔ v 0 ∈ B ∧
        (∀ i : Fin m, v i.succ - v i.castSucc = (0, 1) ∨
          v i.succ - v i.castSucc = (0, -1) ∨
          v i.succ - v i.castSucc = (-1, 0) ∨
          v i.succ - v i.castSucc = (1, 0)) ∧
        (∀ (i : ℕ) (hi : i + 2 ≤ m),
          v ⟨i + 2, by omega⟩ ≠ v ⟨i, by omega⟩)) ∧
      W.card ≤ B.card * 4 * 3 ^ (m - 1) := by
  classical
  choose W hW hcard using fun x => exists_finset_nonbacktracking_walks x m hm
  have hdisj : (B : Set Lattice).PairwiseDisjoint W := by
    intro x _ y _ hxy
    apply Finset.disjoint_left.mpr
    intro v hvx hvy
    exact hxy (((hW x v).mp hvx).1.symm.trans ((hW y v).mp hvy).1)
  refine ⟨B.biUnion W, ?_, ?_⟩
  · intro v
    simp only [Finset.mem_biUnion, hW]
    constructor
    · rintro ⟨x, hx, he, hs, hn⟩
      exact ⟨he ▸ hx, hs, hn⟩
    · rintro ⟨hx, hs, hn⟩
      exact ⟨v 0, hx, rfl, hs, hn⟩
  · rw [Finset.card_biUnion hdisj]
    calc
      ∑ x ∈ B, (W x).card ≤ ∑ _x ∈ B, 4 * 3 ^ (m - 1) :=
        Finset.sum_le_sum (fun x _ => hcard x)
      _ = B.card * 4 * 3 ^ (m - 1) := by
        rw [Finset.sum_const_nat (fun _ _ => rfl), Nat.mul_assoc]

end LPPDifferentiability
