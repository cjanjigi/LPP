/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

/-! The unused-edge construction of a closed directed trail. -/

public section

namespace LPPDifferentiability

open scoped BigOperators

/-- Counting a predicate on an injective finite edge image counts its indices. -/
theorem finite_image_filter_card {A B : Type*} [Fintype A] [DecidableEq B]
    (f : A → B) (hf : Function.Injective f) (p : B → Prop) [DecidablePred p] :
    ((Finset.univ.image f).filter p).card = ∑ i, if p (f i) then 1 else 0 := by
  classical
  rw [Finset.filter_image, Finset.card_image_of_injective _ hf]
  simp [Finset.sum_boole]

/-- Endpoint indicators telescope along an edge-simple vertex family. -/
theorem directed_trail_endpoint_count {V : Type*} [DecidableEq V]
    (m : ℕ) (v : Fin (m + 1) → V)
    (hi : Function.Injective (fun i : Fin m => (v i.castSucc, v i.succ))) (x : V) :
    ((Finset.univ.image (fun i : Fin m => (v i.castSucc, v i.succ))).filter
      (fun e => e.1 = x)).card + (if v (Fin.last m) = x then 1 else 0) =
    ((Finset.univ.image (fun i : Fin m => (v i.castSucc, v i.succ))).filter
      (fun e => e.2 = x)).card + (if v 0 = x then 1 else 0) := by
  classical
  rw [finite_image_filter_card _ hi, finite_image_filter_card _ hi]
  change (∑ i : Fin m, if v i.castSucc = x then 1 else 0) +
      (if v (Fin.last m) = x then 1 else 0) =
    (∑ i : Fin m, if v i.succ = x then 1 else 0) + (if v 0 = x then 1 else 0)
  calc
    _ = ∑ i : Fin (m + 1), if v i = x then 1 else 0 :=
      (Fin.sum_univ_castSucc _).symm
    _ = _ := by rw [Fin.sum_univ_succ, Nat.add_comm]

/-- The length bound follows from the directed edge image in E. -/
theorem directed_trail_length_le {V : Type*} [DecidableEq V]
    (E : Finset (V × V)) (m : ℕ) (v : Fin (m + 1) → V)
    (hi : Function.Injective (fun i : Fin m => (v i.castSucc, v i.succ)))
    (he : ∀ i : Fin m, (v i.castSucc, v i.succ) ∈ E) : m ≤ E.card := by
  have hs : Finset.univ.image (fun i : Fin m => (v i.castSucc, v i.succ)) ⊆ E := by
    intro e h
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
    exact he i
  simpa only [Finset.card_image_of_injective _ hi, Finset.card_univ, Fintype.card_fin]
    using Finset.card_le_card hs

/-- Appending a vertex preserves all old edges and appends the final edge. -/
theorem directed_trail_snoc_edges {V : Type*} (m : ℕ) (v : Fin (m + 1) → V) (z : V) :
    (fun i : Fin (m + 1) =>
      (Fin.snoc (α := fun _ => V) v z i.castSucc, Fin.snoc (α := fun _ => V) v z i.succ)) =
      Fin.snoc (α := fun _ => V × V) (fun i : Fin m => (v i.castSucc, v i.succ)) (v (Fin.last m), z) := by
  funext i
  induction i using Fin.lastCases with
  | last => simp
  | cast i => simp only [Fin.succ_castSucc, Fin.snoc_castSucc]

/-- In a nonempty finite balanced directed edge set, a positive closed edge-simple
vertex family exists. Vertices may repeat, and loops are allowed. -/
theorem finite_balanced_closed_trail {V : Type*} [DecidableEq V]
    (E : Finset (V × V)) (hne : E.Nonempty)
    (hb : ∀ x : V, (E.filter (fun e => e.1 = x)).card =
      (E.filter (fun e => e.2 = x)).card) :
    ∃ (m : ℕ) (v : Fin (m + 1) → V), 0 < m ∧ v 0 = v (Fin.last m) ∧
      Function.Injective (fun i : Fin m => (v i.castSucc, v i.succ)) ∧
      ∀ i : Fin m, (v i.castSucc, v i.succ) ∈ E := by
  classical
  let P : ℕ → Prop := fun m => 0 < m ∧ ∃ v : Fin (m + 1) → V,
    Function.Injective (fun i : Fin m => (v i.castSucc, v i.succ)) ∧
      ∀ i : Fin m, (v i.castSucc, v i.succ) ∈ E
  have hp : P 1 := by
    obtain ⟨e, he⟩ := hne
    refine ⟨by omega, ![e.1, e.2], ?_, ?_⟩
    · exact fun i j _ => Subsingleton.elim i j
    · intro i
      fin_cases i
      simpa using he
  let m := Nat.findGreatest P E.card
  obtain ⟨hm, v, hi, he⟩ : P m :=
    Nat.findGreatest_spec (Finset.card_pos.mpr hne) hp
  have hmax (k : ℕ) (hk : P k) : k ≤ m := by
    have hkc := hk
    obtain ⟨_, w, hw, hwe⟩ := hkc
    exact Nat.le_findGreatest (directed_trail_length_le E k w hw hwe) hk
  refine ⟨m, v, hm, ?_, hi, he⟩
  by_contra hn
  let U := Finset.univ.image (fun i : Fin m => (v i.castSucc, v i.succ))
  have hUE : U ⊆ E := by
    intro e h
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
    exact he i
  have ht := directed_trail_endpoint_count m v hi (v (Fin.last m))
  have hfirst : v 0 ≠ v (Fin.last m) := hn
  have hcounts : (U.filter (fun e => e.1 = v (Fin.last m))).card + 1 =
      (U.filter (fun e => e.2 = v (Fin.last m))).card := by
    simpa [U, hfirst] using ht
  have hout : ∃ z, (v (Fin.last m), z) ∈ E ∧ (v (Fin.last m), z) ∉ U := by
    by_contra h
    push Not at h
    have ho : E.filter (fun e => e.1 = v (Fin.last m)) ⊆
        U.filter (fun e => e.1 = v (Fin.last m)) := by
      intro e hh
      obtain ⟨hee, hxe⟩ := Finset.mem_filter.mp hh
      apply Finset.mem_filter.mpr
      refine ⟨?_, hxe⟩
      have hpair : e = (v (Fin.last m), e.2) := Prod.ext hxe rfl
      rw [hpair] at hee ⊢
      exact h e.2 hee
    have hin : U.filter (fun e => e.2 = v (Fin.last m)) ⊆
        E.filter (fun e => e.2 = v (Fin.last m)) :=
      Finset.filter_subset_filter _ hUE
    have hc₁ := Finset.card_le_card ho
    have hc₂ := Finset.card_le_card hin
    have hc₃ := hb (v (Fin.last m))
    omega
  obtain ⟨z, hz, hzu⟩ := hout
  have hzr : (v (Fin.last m), z) ∉
      Set.range (fun i : Fin m => (v i.castSucc, v i.succ)) := by
    rintro ⟨i, h⟩
    apply hzu
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h⟩
  have hext : P (m + 1) := by
    refine ⟨by omega, Fin.snoc (α := fun _ => V) v z, ?_, ?_⟩
    · rw [directed_trail_snoc_edges]
      exact Fin.snoc_injective_of_injective hi hzr
    · intro i
      have hh := congrFun (directed_trail_snoc_edges m v z) i
      rw [hh]
      induction i using Fin.lastCases with
      | last => simpa using hz
      | cast i => simpa using he i
  have := hmax (m + 1) hext
  omega

end LPPDifferentiability
