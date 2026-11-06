/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.Lattice
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-! Natural left-square labels determined by the edges of a finite walk. -/

public section

namespace LPPDifferentiability

/-- The finite set is constructed from the walk alone. Its complete membership
rule also covers walks whose upward or leftward edges have no natural left cell.
For every label map from the source, it agrees with the source image. -/
theorem exists_contour_natural_labels
    (m : ℕ) (v : Fin (m + 1) → Lattice)
    (hbox : ∀ i, 0 ≤ (v i).1 ∧ (v i).1 ≤ (m : ℤ) + 1 ∧
      0 ≤ (v i).2 ∧ (v i).2 ≤ (m : ℤ) + 1) :
    ∃ B : Finset (ℕ × ℕ),
      (∀ x : ℕ × ℕ, x ∈ B ↔ ∃ i : Fin m,
        (v i.castSucc = ((x.1 : ℤ) + 1, (x.2 : ℤ)) ∧
          v i.succ = ((x.1 : ℤ) + 1, (x.2 : ℤ) + 1)) ∨
        (v i.castSucc = ((x.1 : ℤ) + 1, (x.2 : ℤ) + 1) ∧
          v i.succ = ((x.1 : ℤ), (x.2 : ℤ) + 1))) ∧
      B.card ≤ m ∧
      (∀ C : Finset (ℕ × ℕ),
        (∀ x : ℕ × ℕ, x ∈ C ↔ ∃ i : Fin m,
          (v i.castSucc = ((x.1 : ℤ) + 1, (x.2 : ℤ)) ∧
            v i.succ = ((x.1 : ℤ) + 1, (x.2 : ℤ) + 1)) ∨
          (v i.castSucc = ((x.1 : ℤ) + 1, (x.2 : ℤ) + 1) ∧
            v i.succ = ((x.1 : ℤ), (x.2 : ℤ) + 1))) → C = B) ∧
      (∀ w : Fin m → ℕ × ℕ,
        (∀ i : Fin m,
          (v i.succ - v i.castSucc = (0, 1) →
            v i.castSucc = (((w i).1 : ℤ) + 1, ((w i).2 : ℤ)) ∧
            v i.succ = (((w i).1 : ℤ) + 1, ((w i).2 : ℤ) + 1)) ∧
          (v i.succ - v i.castSucc = (-1, 0) →
            v i.castSucc = (((w i).1 : ℤ) + 1, ((w i).2 : ℤ) + 1) ∧
            v i.succ = (((w i).1 : ℤ), ((w i).2 : ℤ) + 1))) →
        B = ((Finset.univ.filter (fun i : Fin m =>
          v i.succ - v i.castSucc = (0, 1))) ∪
          (Finset.univ.filter (fun i : Fin m =>
          v i.succ - v i.castSucc = (-1, 0)))).image w) := by
  classical
  let R (i : Fin m) (x : ℕ × ℕ) : Prop :=
    (v i.castSucc = ((x.1 : ℤ) + 1, (x.2 : ℤ)) ∧
      v i.succ = ((x.1 : ℤ) + 1, (x.2 : ℤ) + 1)) ∨
    (v i.castSucc = ((x.1 : ℤ) + 1, (x.2 : ℤ) + 1) ∧
      v i.succ = ((x.1 : ℤ), (x.2 : ℤ) + 1))
  have huniq (i : Fin m) (x y : ℕ × ℕ) (hx : R i x) (hy : R i y) : x = y := by
    rcases hx with ⟨hx0, hx1⟩ | ⟨hx0, hx1⟩ <;>
      rcases hy with ⟨hy0, hy1⟩ | ⟨hy0, hy1⟩ <;>
      have ha := hx0.symm.trans hy0 <;>
      have hb := hx1.symm.trans hy1 <;>
      simp only [Prod.mk.injEq] at ha hb <;>
      apply Prod.ext <;> omega
  let B := ((Finset.range (m + 2)).product (Finset.range (m + 2))).filter
    (fun x => ∃ i, R i x)
  have hmem (x : ℕ × ℕ) : x ∈ B ↔ ∃ i, R i x := by
    constructor
    · intro hx
      exact (Finset.mem_filter.mp hx).2
    · rintro ⟨i, hi⟩
      refine Finset.mem_filter.mpr ⟨?_, i, hi⟩
      have hb := hbox i.castSucc
      apply Finset.mem_product.mpr
      simp only [Finset.mem_range]
      rcases hi with ⟨ha, _⟩ | ⟨ha, _⟩ <;>
        rw [ha] at hb <;> constructor <;> omega
  have hcard : B.card ≤ m := by
    let f : B → (Finset.univ : Finset (Fin m)) := fun x =>
      ⟨Classical.choose ((hmem x).mp x.property), Finset.mem_univ _⟩
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      have hx := Classical.choose_spec ((hmem x).mp x.property)
      have hy := Classical.choose_spec ((hmem y).mp y.property)
      have he : (f x).val = (f y).val := congrArg Subtype.val hxy
      change Classical.choose ((hmem x).mp x.property) =
        Classical.choose ((hmem y).mp y.property) at he
      rw [← he] at hy
      exact huniq _ _ _ hx hy
    have hc := Finset.card_le_card_of_injective hf
    simpa only [Finset.card_univ, Fintype.card_fin] using hc
  refine ⟨B, hmem, hcard, ?_, ?_⟩
  · intro C hC
    exact Finset.ext (fun x => (hC x).trans (hmem x).symm)
  · intro w hw
    apply Finset.ext
    intro x
    rw [hmem]
    constructor
    · rintro ⟨i, hi⟩
      have hd : v i.succ - v i.castSucc = (0, 1) ∨
          v i.succ - v i.castSucc = (-1, 0) := by
        rcases hi with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · left
          rw [ha, hb]
          apply Prod.ext <;> simp only [Prod.fst_sub, Prod.snd_sub] <;> omega
        · right
          rw [ha, hb]
          apply Prod.ext <;> simp only [Prod.fst_sub, Prod.snd_sub] <;> omega
      have hwi : R i (w i) := hd.elim
        (fun hu => Or.inl ((hw i).1 hu)) (fun hl => Or.inr ((hw i).2 hl))
      refine Finset.mem_image.mpr ⟨i, ?_, huniq i (w i) x hwi hi⟩
      simpa only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
        true_and] using hd
    · intro hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      refine ⟨i, ?_⟩
      have hd : v i.succ - v i.castSucc = (0, 1) ∨
          v i.succ - v i.castSucc = (-1, 0) := by
        simpa only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
          true_and] using hi
      exact hd.elim (fun hu => Or.inl ((hw i).1 hu))
        (fun hl => Or.inr ((hw i).2 hl))

end LPPDifferentiability
