/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.LatticeBoxCardinality
import Lean.Elab.Tactic.Omega

/-! Greedy finite selection of separated sites with a covering bound. -/

@[expose] public section

namespace LPPDifferentiability

/-- A finite lattice set has a separated subset covering it at the same radius. -/
theorem exists_separated_lattice_subset (S : Finset Lattice) (k : ℕ) :
    ∃ T : Finset Lattice,
      T ⊆ S ∧
      (∀ x ∈ T, ∀ y ∈ T, x ≠ y →
        (k : ℤ) < |x.1 - y.1| ∨ (k : ℤ) < |x.2 - y.2|) ∧
      (∀ x ∈ S, ∃ y ∈ T,
        |x.1 - y.1| ≤ (k : ℤ) ∧ |x.2 - y.2| ≤ (k : ℤ)) ∧
      S.card ≤ (2 * k + 1) ^ 2 * T.card := by
  classical
  refine Finset.strongInductionOn S ?_
  intro S ih
  by_cases hSempty : S = ∅
  · subst S
    refine ⟨∅, by simp, ?_, ?_, ?_⟩
    · intro x hx y hy hxy
      simp at hx
    · intro x hx
      simp at hx
    · simp
  · obtain ⟨v, hvS⟩ := Finset.nonempty_iff_ne_empty.mpr hSempty
    let Q : Finset Lattice :=
      Finset.Icc (v.1 - (k : ℤ)) (v.1 + (k : ℤ)) ×ˢ
        Finset.Icc (v.2 - (k : ℤ)) (v.2 + (k : ℤ))
    let S' : Finset Lattice := S \ Q
    have hQmem (z : Lattice) :
        z ∈ Q ↔
          |v.1 - z.1| ≤ (k : ℤ) ∧ |v.2 - z.2| ≤ (k : ℤ) := by
      simp only [Q, Finset.mem_product, Finset.mem_Icc, abs_le]
      omega
    have hvQ : v ∈ Q := (hQmem v).2 (by simp)
    have hS'sub : S' ⊂ S := by
      constructor
      · exact Finset.sdiff_subset
      · intro hSsub'
        exact (Finset.mem_sdiff.mp (hSsub' hvS)).2 hvQ
    obtain ⟨T', hTsub, hTsep, hTcover, hTcard⟩ := ih S' hS'sub
    have hvnotS' : v ∉ S' := by
      intro hvS'
      exact (Finset.mem_sdiff.mp hvS').2 hvQ
    have hvnotT' : v ∉ T' := fun hvT' => hvnotS' (hTsub hvT')
    have hfar (w : Lattice) (hw : w ∈ T') :
        (k : ℤ) < |v.1 - w.1| ∨ (k : ℤ) < |v.2 - w.2| := by
      have hwnotQ : w ∉ Q := (Finset.mem_sdiff.mp (hTsub hw)).2
      have hnotnear :
          ¬ (|v.1 - w.1| ≤ (k : ℤ) ∧ |v.2 - w.2| ≤ (k : ℤ)) := by
        intro hnear
        exact hwnotQ ((hQmem w).2 hnear)
      rcases not_and_or.mp hnotnear with hfirst | hsecond
      · exact Or.inl (lt_of_not_ge hfirst)
      · exact Or.inr (lt_of_not_ge hsecond)
    refine ⟨insert v T', ?_, ?_, ?_, ?_⟩
    · intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw'
      · exact hvS
      · exact hS'sub.1 (hTsub hw')
    · intro x hx y hy hxy
      simp only [Finset.mem_insert] at hx hy
      rcases hx with rfl | hx'
      · rcases hy with rfl | hy'
        · exact False.elim (hxy rfl)
        · exact hfar y hy'
      · rcases hy with rfl | hy'
        · simpa only [abs_sub_comm] using hfar x hx'
        · exact hTsep x hx' y hy' hxy
    · intro x hxS
      by_cases hxQ : x ∈ Q
      · refine ⟨v, Finset.mem_insert_self v T', ?_⟩
        rcases (hQmem x).mp hxQ with ⟨hfirst, hsecond⟩
        exact ⟨by simpa only [abs_sub_comm] using hfirst,
          by simpa only [abs_sub_comm] using hsecond⟩
      · have hxS' : x ∈ S' := Finset.mem_sdiff.mpr ⟨hxS, hxQ⟩
        obtain ⟨y, hyT, hxy⟩ := hTcover x hxS'
        exact ⟨y, Finset.mem_insert_of_mem hyT, hxy⟩
    · have hQcard : Q.card = (2 * k + 1) ^ 2 := by
        simpa only [Q] using lattice_box_cardinality v k
      have hremoved : (S ∩ Q).card ≤ (2 * k + 1) ^ 2 := by
        calc
          (S ∩ Q).card ≤ Q.card := Finset.card_le_card Finset.inter_subset_right
          _ = (2 * k + 1) ^ 2 := hQcard
      have hsplit : S.card = S'.card + (S ∩ Q).card := by
        symm
        simpa only [S'] using Finset.card_sdiff_add_card_inter S Q
      calc
        S.card = S'.card + (S ∩ Q).card := hsplit
        _ ≤ (2 * k + 1) ^ 2 * T'.card + (2 * k + 1) ^ 2 :=
          Nat.add_le_add hTcard hremoved
        _ = (2 * k + 1) ^ 2 * (T'.card + 1) := by
          rw [Nat.mul_add, Nat.mul_one]
        _ = (2 * k + 1) ^ 2 * (insert v T').card := by
          simp [hvnotT']

end LPPDifferentiability

end
