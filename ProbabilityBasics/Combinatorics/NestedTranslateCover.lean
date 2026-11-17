/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in file LICENSE.
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Prod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Max

/-! A finite covering lemma for nested translates in an additive group. -/

@[expose] public section

open scoped BigOperators

namespace ProbabilityBasics

/-- From finite centers and nested finite sets, choose disjoint translates
whose total size controls the number of centers. This is the finite greedy
covering step behind Krengel's Section 6.2, Lemma 2.5, used in JR Appendix B.5. -/
theorem exists_pairwise_disjoint_translates_of_nested_difference_bound
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (S : ℕ → Finset G)
    (hnested : ∀ m n, m ≤ n → S m ⊆ S n)
    (hzero : ∀ n, 0 ∈ S n)
    (C : ℕ)
    (hdiff : ∀ n,
      (((S n).product (S n)).image (fun p : G × G => p.1 - p.2)).card ≤
        C * (S n).card)
    (E : Finset G) (r : G → ℕ) :
    ∃ A : Finset G, A ⊆ E ∧
      (∀ x ∈ A, ∀ y ∈ A, x ≠ y →
        Disjoint ((S (r x)).image (fun v => x + v))
          ((S (r y)).image (fun v => y + v))) ∧
      E.card ≤ C * ∑ x ∈ A, (S (r x)).card := by
  classical
  let T : G → Finset G := fun x => (S (r x)).image (fun v => x + v)
  change ∃ A : Finset G, A ⊆ E ∧
    (∀ x ∈ A, ∀ y ∈ A, x ≠ y → Disjoint (T x) (T y)) ∧
    E.card ≤ C * ∑ x ∈ A, (S (r x)).card

  refine E.strongInductionOn ?_
  intro E ih
  rcases E.eq_empty_or_nonempty with rfl | hE
  · exact ⟨∅, by simp, by simp, by simp⟩
  · -- Choose a center whose index is maximal among the remaining centers.
    obtain ⟨x, hxE, hmax⟩ := Finset.exists_max_image E r hE

    -- The selected translate contains its center because every S n contains 0.
    have hxmem : x ∈ T x := by
      change x ∈ (S (r x)).image (fun v => x + v)
      exact Finset.mem_image.mpr ⟨0, hzero (r x), by simp⟩
    have hnotSelf : ¬ Disjoint (T x) (T x) := by
      intro hdisj
      exact (Finset.disjoint_left.mp hdisj) hxmem hxmem

    -- Keep centers disjoint from x for the recursive step; the rest are counted by a translate.
    let F : Finset G := E.filter fun y => Disjoint (T x) (T y)
    let B : Finset G := E.filter fun y => ¬ Disjoint (T x) (T y)
    have hxnotF : x ∉ F := by
      intro hxF
      exact hnotSelf (Finset.mem_filter.mp hxF).2
    have hFproper : F ⊂ E := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨Finset.filter_subset _ _, ?_⟩
      intro hFE
      apply hxnotF
      rw [hFE]
      exact hxE

    -- Recurse on the proper subset whose translates avoid the selected one.
    obtain ⟨A, hAsub, hPair, hCover⟩ := ih F hFproper

    -- Any intersecting translate has its center in x + (S (r x) - S (r x)).
    let D : Finset G := ((S (r x)).product (S (r x))).image
      (fun p : G × G => p.1 - p.2)
    let U : Finset G := D.image (fun d => x + d)
    have hinter (y : G) (hyB : y ∈ B) :
        ∃ z, z ∈ T x ∧ z ∈ T y := by
      have hbad : ¬ Disjoint (T x) (T y) := (Finset.mem_filter.mp hyB).2
      by_contra hno
      apply hbad
      apply Finset.disjoint_left.mpr
      intro z hzX hzY
      exact hno ⟨z, hzX, hzY⟩

    have hBsubset : B ⊆ U := by
      intro y hyB
      obtain ⟨z, hzX, hzY⟩ := hinter y hyB
      obtain ⟨u, hu, hxu⟩ := Finset.mem_image.mp hzX
      obtain ⟨v, hv, hyv⟩ := Finset.mem_image.mp hzY
      have hyE : y ∈ E := (Finset.mem_filter.mp hyB).1
      have hvX : v ∈ S (r x) := hnested (r y) (r x) (hmax y hyE) hv
      have hcommon : x + u = y + v := hxu.trans hyv.symm
      have hyEq : y = x + (u - v) := by
        calc
          y = (y + v) - v := by simp
          _ = (x + u) - v := by rw [← hcommon]
          _ = x + (u - v) := add_sub_assoc _ _ _
      have hdiffmem : u - v ∈ D := by
        change u - v ∈ ((S (r x)).product (S (r x))).image
          (fun p : G × G => p.1 - p.2)
        exact Finset.mem_image.mpr
          ⟨(u, v), Finset.mem_product.mpr ⟨hu, hvX⟩, rfl⟩
      change y ∈ D.image (fun d => x + d)
      exact Finset.mem_image.mpr ⟨u - v, hdiffmem, hyEq.symm⟩

    have hUcard : U.card = D.card := by
      change (D.image (fun d => x + d)).card = D.card
      exact Finset.card_image_of_injective D (by
        intro a b hab
        exact add_left_cancel hab)
    have hBcard : B.card ≤ C * (S (r x)).card := by
      calc
        B.card ≤ U.card := Finset.card_le_card hBsubset
        _ = D.card := hUcard
        _ ≤ C * (S (r x)).card := hdiff (r x)

    -- Partition E into the recursive centers and the centers already counted by the difference set.
    have hpartition : F.card + B.card = E.card := by
      dsimp only [F, B]
      exact Finset.card_filter_add_card_filter_not (s := E)
        (fun y => Disjoint (T x) (T y))

    have hxnotA : x ∉ A := fun hxA => hxnotF (hAsub hxA)
    have hsum : (∑ y ∈ insert x A, (S (r y)).card) =
        (S (r x)).card + ∑ y ∈ A, (S (r y)).card := by
      rw [Finset.sum_insert hxnotA]

    -- Add the selected center and combine the two cardinality bounds.
    have htotal : E.card ≤ C * (S (r x)).card + C * ∑ y ∈ A, (S (r y)).card := by
      calc
        E.card = F.card + B.card := hpartition.symm
        _ ≤ C * ∑ y ∈ A, (S (r y)).card + C * (S (r x)).card :=
          Nat.add_le_add hCover hBcard
        _ = C * (S (r x)).card + C * ∑ y ∈ A, (S (r y)).card := by
          exact Nat.add_comm _ _
    have hfinal : E.card ≤ C * ∑ y ∈ insert x A, (S (r y)).card := by
      calc
        E.card ≤ C * ((S (r x)).card + ∑ y ∈ A, (S (r y)).card) := by
          simpa only [Nat.mul_add] using htotal
        _ = C * ∑ y ∈ insert x A, (S (r y)).card := by rw [← hsum]

    refine ⟨insert x A,
      Finset.insert_subset hxE (hAsub.trans (Finset.filter_subset _ _)),
      ?_, hfinal⟩
    intro a ha b hb hab
    simp only [Finset.mem_insert] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact False.elim (hab rfl)
      · exact (Finset.mem_filter.mp (hAsub hb)).2
    · rcases hb with rfl | hb
      · exact (Finset.mem_filter.mp (hAsub ha)).2.symm
      · exact hPair a ha b hb hab

end ProbabilityBasics
