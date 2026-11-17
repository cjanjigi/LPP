/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in file LICENSE.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import ProbabilityBasics.Combinatorics.IntegerRectangles
public import ProbabilityBasics.Combinatorics.NestedTranslateCover
import Mathlib.Tactic

/-! A finite weighted count for nested integer prefix rectangles. -/

@[expose] public section

open scoped BigOperators

namespace ProbabilityBasics

/-- The bad centers for nested integer rectangles have the exact finite
weighted count bound used before maximal transference, following the finite
covering route in Krengel's Section 6.2 cited by JR Appendix B.5. -/
theorem weighted_rectangle_weak_count
    (a b : ℕ → ℕ) (ha : Monotone a) (hb : Monotone b)
    (A B : Finset (ℤ × ℤ)) (N : ℕ) (w : ℤ × ℤ → ℝ)
    (hw : ∀ v, 0 ≤ w v) (t : ℝ) (ht : 0 < t) :
    let R : ℕ → Finset (ℤ × ℤ) := fun n =>
      (Finset.Ico (0 : ℤ) (a n : ℤ)).product
        (Finset.Ico (0 : ℤ) (b n : ℤ))
    (∀ u ∈ A, ∀ n ∈ Finset.Icc 1 N, ∀ v ∈ R n, u + v ∈ B) →
    let Bad : ℤ × ℤ → Prop := fun u =>
      ∃ n ∈ Finset.Icc 1 N, (R n).Nonempty ∧
        t * ((R n).card : ℝ) < ∑ v ∈ R n, w (u + v)
    letI : DecidablePred Bad := Classical.decPred Bad
    t * (((A.filter Bad).card : ℕ) : ℝ) ≤ 4 * ∑ v ∈ B, w v := by
  classical
  dsimp only
  intro hContain
  let R : ℕ → Finset (ℤ × ℤ) := fun n =>
    (Finset.Ico (0 : ℤ) (a n : ℤ)).product
      (Finset.Ico (0 : ℤ) (b n : ℤ))
  change (∀ u ∈ A, ∀ n ∈ Finset.Icc 1 N, ∀ v ∈ R n, u + v ∈ B) at hContain
  let Bad : ℤ × ℤ → Prop := fun u =>
    ∃ n ∈ Finset.Icc 1 N, (R n).Nonempty ∧
      t * ((R n).card : ℝ) < ∑ v ∈ R n, w (u + v)
  let : DecidablePred Bad := Classical.decPred Bad
  change t * (((A.filter Bad).card : ℕ) : ℝ) ≤ 4 * ∑ v ∈ B, w v

  have hRect (n : ℕ) := integer_rectangle_difference_regularities (a n) (b n)
  have hRcard (n : ℕ) : (R n).card = a n * b n := by
    exact (hRect n).1
  have hRzero (n : ℕ) :
      ((0, 0) ∈ R n ↔ 0 < a n ∧ 0 < b n) := by
    exact (hRect n).2.1
  have hRsubset (m n : ℕ) (hmn : m ≤ n) : R m ⊆ R n := by
    exact (hRect m).2.2.1 (a n) (b n) (ha hmn) (hb hmn)
  have hRdiff (n : ℕ) :
      (Finset.image (fun p : (ℤ × ℤ) × (ℤ × ℤ) => p.1 - p.2)
        ((R n).product (R n))).card ≤ 4 * (R n).card := by
    exact (hRect n).2.2.2

  let S : ℕ → Finset (ℤ × ℤ) := fun n => insert (0, 0) (R n)
  have hSzero : ∀ n, (0, 0) ∈ S n := by
    intro n
    simp [S]
  have hSnested : ∀ m n, m ≤ n → S m ⊆ S n := by
    intro m n hmn z hz
    change z ∈ insert (0, 0) (R m) at hz
    change z ∈ insert (0, 0) (R n)
    rcases Finset.mem_insert.mp hz with hz0 | hzR
    · exact Finset.mem_insert.mpr (Or.inl hz0)
    · exact Finset.mem_insert.mpr (Or.inr (hRsubset m n hmn hzR))
  have hRorigin (n : ℕ) (hn : (R n).Nonempty) : (0, 0) ∈ R n := by
    have hcard : 0 < (R n).card := Finset.card_pos.mpr hn
    rw [hRcard n] at hcard
    have haPos : 0 < a n := by
      by_contra h
      have hz : a n = 0 := Nat.eq_zero_of_not_pos h
      simp [hz] at hcard
    have hbPos : 0 < b n := by
      by_contra h
      have hz : b n = 0 := Nat.eq_zero_of_not_pos h
      simp [hz] at hcard
    exact (hRzero n).2 ⟨haPos, hbPos⟩
  have hSeq (n : ℕ) (hn : (R n).Nonempty) : S n = R n := by
    simp [S, hRorigin n hn]
  have hSdiff (n : ℕ) :
      (Finset.image (fun p : (ℤ × ℤ) × (ℤ × ℤ) => p.1 - p.2)
        ((S n).product (S n))).card ≤ 4 * (S n).card := by
    by_cases hn : (R n).Nonempty
    · rw [hSeq n hn]
      exact hRdiff n
    · have hEmpty : R n = ∅ := by
        by_contra hne
        exact hn (Finset.nonempty_iff_ne_empty.mpr hne)
      norm_num [S, hEmpty]

  let E : Finset (ℤ × ℤ) := A.filter Bad
  have hEsubA : E ⊆ A := by
    intro u hu
    exact (Finset.mem_filter.mp hu).1
  have hBadWitness (u : ℤ × ℤ) (hu : u ∈ E) :
      ∃ n ∈ Finset.Icc 1 N, (R n).Nonempty ∧
        t * ((R n).card : ℝ) < ∑ v ∈ R n, w (u + v) := by
    exact (Finset.mem_filter.mp hu).2
  let r : (ℤ × ℤ) → ℕ := fun u =>
    if hu : u ∈ E then Classical.choose (hBadWitness u hu) else 0
  have hr (u : ℤ × ℤ) (hu : u ∈ E) :
      r u ∈ Finset.Icc 1 N ∧ (R (r u)).Nonempty ∧
        t * ((R (r u)).card : ℝ) < ∑ v ∈ R (r u), w (u + v) := by
    simpa [r, hu] using Classical.choose_spec (hBadWitness u hu)

  obtain ⟨Chosen, hChosenSub, hChosenDisj, hCover⟩ :=
    exists_pairwise_disjoint_translates_of_nested_difference_bound
      S hSnested hSzero 4 hSdiff E r
  have hSChosen (x : ℤ × ℤ) (hx : x ∈ Chosen) : S (r x) = R (r x) :=
    hSeq (r x) (hr x (hChosenSub hx)).2.1
  let T : (ℤ × ℤ) → Finset (ℤ × ℤ) := fun x =>
    (R (r x)).image (fun v => x + v)
  have hTdisj : ∀ x ∈ Chosen, ∀ y ∈ Chosen, x ≠ y → Disjoint (T x) (T y) := by
    intro x hx y hy hxy
    simpa [T, hSChosen x hx, hSChosen y hy] using hChosenDisj x hx y hy hxy
  have hCoverR : E.card ≤ 4 * ∑ x ∈ Chosen, (R (r x)).card := by
    have hCardSum :
        (∑ x ∈ Chosen, (S (r x)).card) = ∑ x ∈ Chosen, (R (r x)).card := by
      apply Finset.sum_congr rfl
      intro x hx
      exact congrArg Finset.card (hSChosen x hx)
    simpa only [hCardSum] using hCover

  let U : Finset (ℤ × ℤ) := Chosen.biUnion T
  have hTsubB : ∀ x ∈ Chosen, T x ⊆ B := by
    intro x hx z hz
    rcases Finset.mem_image.mp hz with ⟨v, hv, rfl⟩
    exact hContain x (hEsubA (hChosenSub hx)) (r x)
      (hr x (hChosenSub hx)).1 v hv
  have hUsubB : U ⊆ B := by
    intro z hz
    rcases Finset.mem_biUnion.mp hz with ⟨x, hx, hxz⟩
    exact hTsubB x hx hxz
  have hPairwiseT : (Chosen : Set (ℤ × ℤ)).PairwiseDisjoint T := by
    intro x hx y hy hxy
    exact hTdisj x hx y hy hxy
  have hSumTranslate (x : ℤ × ℤ) :
      (∑ z ∈ T x, w z) = ∑ v ∈ R (r x), w (x + v) := by
    simpa [T] using
      (Finset.sum_image (s := R (r x)) (g := fun v => x + v)
        (f := w) (fun _ _ _ _ h => add_left_cancel h))
  have hSumUnion :
      (∑ z ∈ U, w z) = ∑ x ∈ Chosen, ∑ z ∈ T x, w z := by
    simpa [U] using (Finset.sum_biUnion (s := Chosen) (t := T)
      (f := w) hPairwiseT)
  have hSumWeight :
      (∑ x ∈ Chosen, ∑ v ∈ R (r x), w (x + v)) ≤ ∑ z ∈ B, w z := by
    calc
      (∑ x ∈ Chosen, ∑ v ∈ R (r x), w (x + v)) = ∑ z ∈ U, w z := by
        calc
          (∑ x ∈ Chosen, ∑ v ∈ R (r x), w (x + v)) =
              ∑ x ∈ Chosen, ∑ z ∈ T x, w z := by
            apply Finset.sum_congr rfl
            intro x hx
            exact (hSumTranslate x).symm
          _ = ∑ z ∈ U, w z := hSumUnion.symm
      _ ≤ ∑ z ∈ B, w z :=
        Finset.sum_le_sum_of_subset_of_nonneg hUsubB (fun z _ _ => hw z)
  have hSumThreshold :
      (∑ x ∈ Chosen, t * ((R (r x)).card : ℝ)) ≤
        ∑ x ∈ Chosen, ∑ v ∈ R (r x), w (x + v) := by
    apply Finset.sum_le_sum
    intro x hx
    exact (hr x (hChosenSub hx)).2.2.le
  have hCoverReal :
      (E.card : ℝ) ≤ 4 * ∑ x ∈ Chosen, ((R (r x)).card : ℝ) := by
    exact_mod_cast hCoverR
  calc
    t * (E.card : ℝ) ≤ t * (4 * ∑ x ∈ Chosen, ((R (r x)).card : ℝ)) :=
      mul_le_mul_of_nonneg_left hCoverReal ht.le
    _ = 4 * (t * ∑ x ∈ Chosen, ((R (r x)).card : ℝ)) := by ring
    _ = 4 * ∑ x ∈ Chosen, t * ((R (r x)).card : ℝ) := by rw [Finset.mul_sum]
    _ ≤ 4 * ∑ x ∈ Chosen, ∑ v ∈ R (r x), w (x + v) := by
      exact mul_le_mul_of_nonneg_left hSumThreshold (by norm_num)
    _ ≤ 4 * ∑ z ∈ B, w z := by
      exact mul_le_mul_of_nonneg_left hSumWeight (by norm_num)

end ProbabilityBasics
