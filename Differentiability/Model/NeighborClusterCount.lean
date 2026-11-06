/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.Environment
public import Mathlib.Data.Finset.Prod
public import Mathlib.Logic.Relation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Chains of very bad sites in a connected cluster

A finite set of sites that is connected for the relation "l1-distance at most
`d0`" and has more than `K` elements contains a chain of `K + 1` distinct sites
in which every site after the first is within `d0` of an earlier one. The
number of such chains starting at a given site is at most
`K! (2 d0 + 1) ^ (2 K)`: each new site is chosen as an earlier site (at most
`K` choices at the last step) plus an offset in the box `[-d0, d0] ^ 2`.
-/

public section

namespace LPPDifferentiability

/-- The chain condition, used inside proofs only: every site after the first is
within `d0` of an earlier one. -/
private def CloseChain (d0 : ℕ) {n : ℕ} (f : Fin n → Lattice) : Prop :=
  ∀ i : Fin n, 0 < i.val → ∃ j : Fin n, j.val < i.val ∧
    |(f i).1 - (f j).1| + |(f i).2 - (f j).2| ≤ (d0 : ℤ)

/-- A path of a relation from inside a set to outside it leaves the set by one edge. -/
private theorem exists_edge_leaving {α : Type*} (r : α → α → Prop) (A : Set α)
    {x y : α} (h : Relation.ReflTransGen r x y) (hx : x ∈ A) (hy : y ∉ A) :
    ∃ a ∈ A, ∃ b, b ∉ A ∧ r a b := by
  revert hy
  induction h with
  | refl => intro hy; exact absurd hx hy
  | @tail b c _ hbc ih =>
    intro hy
    by_cases hb : b ∈ A
    · exact ⟨b, hb, c, hy, hbc⟩
    · exact ih hb

private theorem closeChain_snoc {d0 m : ℕ} (f : Fin (m + 1) → Lattice) (hf : CloseChain d0 f)
    (b : Lattice) (a' : Fin (m + 1))
    (hab : |(b.1) - (f a').1| + |(b.2) - (f a').2| ≤ (d0 : ℤ)) :
    CloseChain d0 (Fin.snoc (α := fun _ => Lattice) f b : Fin (m + 2) → Lattice) := by
  intro i hi
  induction i using Fin.lastCases with
  | last =>
    refine ⟨a'.castSucc, ?_, ?_⟩
    · simp
    · simpa only [Fin.snoc_last, Fin.snoc_castSucc] using hab
  | cast i' =>
    obtain ⟨j', hj', hd⟩ := hf i' (by simpa using hi)
    exact ⟨j'.castSucc, by simpa using hj', by simpa only [Fin.snoc_castSucc] using hd⟩

private theorem exists_closeChain_in {d0 : ℕ} (S : Finset Lattice)
    (hconn : ∀ x ∈ S, ∀ y ∈ S, Relation.ReflTransGen
      (fun a b : Lattice => a ∈ S ∧ b ∈ S ∧ |a.1 - b.1| + |a.2 - b.2| ≤ (d0 : ℤ)) x y) :
    ∀ m : ℕ, m + 1 ≤ S.card → ∃ f : Fin (m + 1) → Lattice,
      Function.Injective f ∧ (∀ i, f i ∈ S) ∧ CloseChain d0 f := by
  classical
  intro m
  induction m with
  | zero =>
    intro hcard
    have hpos : 0 < S.card := by omega
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
    refine ⟨fun _ => x, fun a b _ => (Fin.eq_zero a).trans (Fin.eq_zero b).symm, fun _ => hx, ?_⟩
    intro i hi
    exfalso
    have := i.isLt
    omega
  | succ m ih =>
    intro hcard
    obtain ⟨f, hinj, hS, hchain⟩ := ih (by omega)
    have himg : (Finset.univ.image f).card = m + 1 := by
      rw [Finset.card_image_of_injective _ hinj]
      simp
    have hnot : ¬ S ⊆ Finset.univ.image f := by
      intro hsub
      have := Finset.card_le_card hsub
      omega
    obtain ⟨y, hyS, hyimg⟩ := Finset.not_subset.mp hnot
    obtain ⟨a, haA, b, hbA, hab, hbS, hclose⟩ := exists_edge_leaving
      (fun a b : Lattice => a ∈ S ∧ b ∈ S ∧ |a.1 - b.1| + |a.2 - b.2| ≤ (d0 : ℤ))
      (↑(Finset.univ.image f) : Set Lattice) (hconn (f 0) (hS 0) y hyS)
      (by simp) (by simpa using hyimg)
    obtain ⟨a', ha'⟩ : ∃ a', f a' = a := by simpa using haA
    have hbimg : ∀ i, f i ≠ b := fun i hi => hbA (by simp [← hi])
    have hclose' : |b.1 - (f a').1| + |b.2 - (f a').2| ≤ (d0 : ℤ) := by
      rw [ha', abs_sub_comm b.1, abs_sub_comm b.2]
      exact hclose
    refine ⟨Fin.snoc (α := fun _ => Lattice) f b, ?_, ?_, closeChain_snoc f hchain b a' hclose'⟩
    · intro i j hij
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => rfl
        | cast j' =>
          simp only [Fin.snoc_last, Fin.snoc_castSucc] at hij
          exact absurd hij.symm (hbimg j')
      | cast i' =>
        induction j using Fin.lastCases with
        | last =>
          simp only [Fin.snoc_last, Fin.snoc_castSucc] at hij
          exact absurd hij (hbimg i')
        | cast j' =>
          simp only [Fin.snoc_castSucc] at hij
          exact congrArg Fin.castSucc (hinj hij)
    · intro i
      induction i using Fin.lastCases with
      | last => simpa only [Fin.snoc_last] using hbS
      | cast i' => simpa only [Fin.snoc_castSucc] using hS i'

/-- A finite set of very bad sites in `Q` that is connected for the relation
"l1-distance at most `d0`" and has more than `K` elements contains a chain of
`K + 1` distinct very bad sites of `Q`, each after the first within `d0` of an
earlier one. -/
theorem exists_close_chain_of_connected_card_gt
    (d0 K : ℕ) (ω : Environment) (T : ℝ) (Q S : Finset Lattice) (hSQ : S ⊆ Q)
    (hbad : ∀ z ∈ S, ω z < -T)
    (hconn : ∀ x ∈ S, ∀ y ∈ S, Relation.ReflTransGen
      (fun a b : Lattice => a ∈ S ∧ b ∈ S ∧ |a.1 - b.1| + |a.2 - b.2| ≤ (d0 : ℤ)) x y)
    (hcard : K < S.card) :
    ∃ f : Fin (K + 1) → Lattice, Function.Injective f ∧
      (∀ i, f i ∈ Q ∧ ω (f i) < -T) ∧
      ∀ i : Fin (K + 1), 0 < i.val → ∃ j : Fin (K + 1), j.val < i.val ∧
        |(f i).1 - (f j).1| + |(f i).2 - (f j).2| ≤ (d0 : ℤ) := by
  obtain ⟨f, hinj, hS, hchain⟩ := exists_closeChain_in S hconn K (by omega)
  exact ⟨f, hinj, fun i => ⟨hSQ (hS i), hbad _ (hS i)⟩, hchain⟩

private theorem exists_closeChain_cover (d0 : ℕ) (x : Lattice) : ∀ K : ℕ,
    ∃ C : Finset (Fin (K + 1) → Lattice),
      (∀ f : Fin (K + 1) → Lattice, f 0 = x → CloseChain d0 f → f ∈ C) ∧
      C.card ≤ K.factorial * (2 * d0 + 1) ^ (2 * K) := by
  classical
  intro K
  induction K with
  | zero =>
    refine ⟨{fun _ => x}, ?_, by simp⟩
    intro f hf _
    have : f = fun _ => x := funext fun i => by
      rw [Fin.eq_zero i]
      exact hf
    simp [this]
  | succ K ih =>
    obtain ⟨C, hC, hcard⟩ := ih
    let box : Finset Lattice := Finset.Icc (-(d0 : ℤ)) d0 ×ˢ Finset.Icc (-(d0 : ℤ)) d0
    have hbox : box.card = (2 * d0 + 1) ^ 2 := by
      simp only [box, Finset.card_product, Int.card_Icc]
      have : ((d0 : ℤ) + 1 - -(d0 : ℤ)).toNat = 2 * d0 + 1 := by omega
      rw [this]
      ring
    refine ⟨(C ×ˢ (Finset.univ ×ˢ box)).image
      (fun p => Fin.snoc (α := fun _ => Lattice) p.1 (p.1 p.2.1 + p.2.2)), ?_, ?_⟩
    · intro f hf0 hfc
      let g : Fin (K + 1) → Lattice := fun i => f i.castSucc
      have hg : CloseChain d0 g := by
        intro i hi
        obtain ⟨j, hj, hd⟩ := hfc i.castSucc (by simpa using hi)
        have hjlt : j.val < K + 1 := by
          have := i.isLt
          simp only [Fin.val_castSucc] at hj
          omega
        exact ⟨⟨j.val, hjlt⟩, by simpa using hj, hd⟩
      have hgC : g ∈ C := hC g hf0 hg
      obtain ⟨j, hj, hd⟩ := hfc (Fin.last (K + 1)) (by simp)
      have hjlt : j.val < K + 1 := by simpa using hj
      let j' : Fin (K + 1) := ⟨j.val, hjlt⟩
      have hjj : j'.castSucc = j := Fin.ext rfl
      have hoff : f (Fin.last (K + 1)) - f j ∈ box := by
        simp only [box, Finset.mem_product, Finset.mem_Icc, Prod.fst_sub, Prod.snd_sub]
        have h1 := abs_nonneg ((f (Fin.last (K + 1))).1 - (f j).1)
        have h2 := abs_nonneg ((f (Fin.last (K + 1))).2 - (f j).2)
        have h3 := abs_le.mp (show |(f (Fin.last (K + 1))).1 - (f j).1| ≤ (d0 : ℤ) by linarith)
        have h4 := abs_le.mp (show |(f (Fin.last (K + 1))).2 - (f j).2| ≤ (d0 : ℤ) by linarith)
        exact ⟨⟨h3.1, h3.2⟩, ⟨h4.1, h4.2⟩⟩
      refine Finset.mem_image.mpr ⟨(g, j', f (Fin.last (K + 1)) - f j), ?_, ?_⟩
      · exact Finset.mem_product.mpr ⟨hgC, Finset.mem_product.mpr ⟨Finset.mem_univ _, hoff⟩⟩
      · show Fin.snoc (α := fun _ => Lattice) g (g j' + (f (Fin.last (K + 1)) - f j)) = f
        have : g j' + (f (Fin.last (K + 1)) - f j) = f (Fin.last (K + 1)) := by
          have : g j' = f j := by
            show f j'.castSucc = f j
            rw [hjj]
          rw [this]
          abel
        rw [this]
        exact Fin.snoc_init_self f
    · calc
        _ ≤ (C ×ˢ (Finset.univ ×ˢ box)).card := Finset.card_image_le
        _ = C.card * ((K + 1) * (2 * d0 + 1) ^ 2) := by
          rw [Finset.card_product, Finset.card_product, hbox]
          simp
        _ ≤ (K.factorial * (2 * d0 + 1) ^ (2 * K)) * ((K + 1) * (2 * d0 + 1) ^ 2) :=
          Nat.mul_le_mul_right _ hcard
        _ = (K + 1).factorial * (2 * d0 + 1) ^ (2 * (K + 1)) := by
          rw [Nat.factorial_succ]
          ring

/-- The chains of `K + 1` distinct sites starting at `x`, each later site within
`d0` of an earlier one, form a finite set with at most `K! (2 d0 + 1) ^ (2 K)`
members. -/
theorem exists_close_chain_finset_card_le (d0 K : ℕ) (x : Lattice) :
    ∃ C : Finset (Fin (K + 1) → Lattice),
      (∀ f : Fin (K + 1) → Lattice, f ∈ C ↔ f 0 = x ∧ Function.Injective f ∧
        ∀ i : Fin (K + 1), 0 < i.val → ∃ j : Fin (K + 1), j.val < i.val ∧
          |(f i).1 - (f j).1| + |(f i).2 - (f j).2| ≤ (d0 : ℤ)) ∧
      C.card ≤ K.factorial * (2 * d0 + 1) ^ (2 * K) := by
  classical
  obtain ⟨C, hC, hcard⟩ := exists_closeChain_cover d0 x K
  refine ⟨C.filter (fun f => f 0 = x ∧ Function.Injective f ∧ CloseChain d0 f), ?_,
    (Finset.card_filter_le _ _).trans hcard⟩
  intro f
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨hC f h.1 h.2.2, h⟩⟩

/-- The chains of `K + 1` distinct sites of `Q` number at most
`|Q| * (K! (2 d0 + 1) ^ (2 K))`. -/
theorem exists_close_chain_finset_card_le_mul_card (d0 K : ℕ) (Q : Finset Lattice) :
    ∃ F : Finset (Fin (K + 1) → Lattice),
      (∀ f : Fin (K + 1) → Lattice, f ∈ F ↔ Function.Injective f ∧ (∀ i, f i ∈ Q) ∧
        ∀ i : Fin (K + 1), 0 < i.val → ∃ j : Fin (K + 1), j.val < i.val ∧
          |(f i).1 - (f j).1| + |(f i).2 - (f j).2| ≤ (d0 : ℤ)) ∧
      F.card ≤ Q.card * (K.factorial * (2 * d0 + 1) ^ (2 * K)) := by
  classical
  choose C hC hcard using fun x : Lattice => exists_close_chain_finset_card_le d0 K x
  refine ⟨(Q.biUnion C).filter (fun f => ∀ i, f i ∈ Q), ?_, ?_⟩
  · intro f
    rw [Finset.mem_filter, Finset.mem_biUnion]
    constructor
    · rintro ⟨⟨x, _, hx⟩, hfQ⟩
      obtain ⟨_, hinj, hchain⟩ := (hC x f).mp hx
      exact ⟨hinj, hfQ, hchain⟩
    · rintro ⟨hinj, hfQ, hchain⟩
      exact ⟨⟨f 0, hfQ 0, (hC (f 0) f).mpr ⟨rfl, hinj, hchain⟩⟩, hfQ⟩
  · calc
      _ ≤ (Q.biUnion C).card := Finset.card_filter_le _ _
      _ ≤ ∑ x ∈ Q, (C x).card := Finset.card_biUnion_le
      _ ≤ ∑ _x ∈ Q, K.factorial * (2 * d0 + 1) ^ (2 * K) :=
        Finset.sum_le_sum fun x _ => hcard x
      _ = Q.card * (K.factorial * (2 * d0 + 1) ^ (2 * K)) := by simp

end LPPDifferentiability
