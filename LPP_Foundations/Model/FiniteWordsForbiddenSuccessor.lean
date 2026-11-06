/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Data.List.Chain
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! Exact counts for finite lists excluding one successor at each step.
Mathlib calls the consecutive-pair property `List.IsChain`.
-/
public section

namespace LPPDifferentiability

private theorem cons_images_pairwise_disjoint {A : Type*} [DecidableEq A]
    (s : Finset A) (T : A → Finset (List A)) :
    (s : Set A).PairwiseDisjoint (fun a => (T a).image (List.cons a)) := by
  intro a _ b _ hab
  apply Finset.disjoint_left.mpr
  intro w hwa hwb
  obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hwa
  obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hwb
  exact hab (List.cons.inj (hu.trans hv.symm)).1

private theorem exists_finset_continuations {A : Type*} [Fintype A] [DecidableEq A]
    (forbidden : A → A) (n : ℕ) :
    ∃ T : A → Finset (List A), ∀ a,
      (∀ w, w ∈ T a ↔ w.length = n ∧
        (a :: w).IsChain (fun x y => y ≠ forbidden x)) ∧
      (T a).card = (Fintype.card A - 1) ^ n := by
  classical
  induction n with
  | zero =>
    refine ⟨fun _ => {[]}, fun a => ⟨?_, ?_⟩⟩
    · intro w
      rw [Finset.mem_singleton, List.length_eq_zero_iff]
      constructor
      · intro hw
        subst w
        exact ⟨rfl, List.isChain_singleton a⟩
      · exact And.left
    · simp only [Finset.card_singleton, pow_zero]
  | succ n ih =>
    obtain ⟨T, hT⟩ := ih
    let S : A → Finset (List A) := fun a =>
      (Finset.univ.erase (forbidden a)).biUnion fun b => (T b).image (List.cons b)
    refine ⟨S, fun a => ⟨?_, ?_⟩⟩
    · intro w
      cases w with
      | nil =>
        simp only [S, Finset.mem_biUnion, Finset.mem_image, List.cons_ne_nil,
          and_false, exists_false, List.length_nil,
          false_and, Nat.zero_ne_add_one]
      | cons b w =>
        simp only [S, Finset.mem_biUnion, Finset.mem_erase, Finset.mem_univ,
          and_true, Finset.mem_image, List.cons.injEq,
          hT, List.length_cons, Nat.add_right_cancel_iff, List.isChain_cons_cons]
        aesop
    · change ((Finset.univ.erase (forbidden a)).biUnion
        fun b => (T b).image (List.cons b)).card = _
      rw [Finset.card_biUnion
        (cons_images_pairwise_disjoint (Finset.univ.erase (forbidden a)) T)]
      simp only [Finset.card_image_of_injective _ List.cons_injective, (hT _).2]
      rw [Finset.sum_const_nat (fun _ _ => rfl),
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, pow_succ]
      exact Nat.mul_comm _ _

/-- All nonempty words with exactly one forbidden successor at each letter,
with their exact cardinality. No regularity of the forbidden map is required. -/
theorem exists_finset_words_forbidden_successor {A : Type*} [Fintype A] [DecidableEq A]
    (forbidden : A → A) (n : ℕ) :
    ∃ W : Finset (List A),
      (∀ w, w ∈ W ↔ w.length = n + 1 ∧
        w.IsChain (fun a b => b ≠ forbidden a)) ∧
      W.card = Fintype.card A * (Fintype.card A - 1) ^ n := by
  classical
  obtain ⟨T, hT⟩ := exists_finset_continuations forbidden n
  let W : Finset (List A) := Finset.univ.biUnion fun a => (T a).image (List.cons a)
  refine ⟨W, ?_, ?_⟩
  · intro w
    cases w with
    | nil =>
      simp only [W, Finset.mem_biUnion, Finset.mem_image, List.cons_ne_nil,
        and_false, exists_false, List.length_nil, Nat.zero_ne_add_one, false_and]
    | cons a w =>
      simp only [W, Finset.mem_biUnion, Finset.mem_univ, true_and,
        Finset.mem_image, List.cons.injEq, hT,
        List.length_cons, Nat.add_right_cancel_iff]
      aesop
  · change (Finset.univ.biUnion fun a => (T a).image (List.cons a)).card = _
    rw [Finset.card_biUnion (cons_images_pairwise_disjoint Finset.univ T)]
    simp only [Finset.card_image_of_injective _ List.cons_injective, (hT _).2]
    rw [Finset.sum_const_nat (fun _ _ => rfl), Finset.card_univ]

/-- For four directions, the forbidden letter is the opposite direction.
The labels are right, up, left, down, so opposition is addition of two. -/
theorem exists_finset_four_direction_words (n : ℕ) :
    ∃ W : Finset (List (Fin 4)),
      (∀ w, w ∈ W ↔ w.length = n + 1 ∧
        w.IsChain (fun a b => b ≠ a + 2)) ∧
      W.card = 4 * 3 ^ n := by
  simpa only [Fintype.card_fin, Nat.reduceSub] using
    exists_finset_words_forbidden_successor (fun a : Fin 4 => a + 2) n

end LPPDifferentiability
