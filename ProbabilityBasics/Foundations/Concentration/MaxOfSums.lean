/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Deterministic facts about the maximum of set sums (Martin 2004, Lemma 3.1)

These are the deterministic ingredients of the proof of Lemma 3.1 of Martin (2004).

Let `C` be a nonempty family of finite sets of indices, and let `y` be a vector with
`|y j| ≤ L` for every `j`. Write `Z(y)` for the maximum over `c ∈ C` of `∑ j ∈ c, y j`.

* `sup_sum_update_neg_le`: lowering one coordinate of `y` to `-L` does not increase `Z`.
* `exists_mem_sup_sum_sub_update_neg_le`: some maximizing set `c` controls the drop of
  `Z` when one coordinate is lowered to `-L`. The drop is at most `2 L` when the coordinate lies in
  `c`, and at most `0` otherwise.
* `sum_exp_mul_sub_sub_one_le` and `sum_exp_neg_mul_add_sub_one_le`: exponential sums over a set
  `c` of size at most `R`, used in the entropy (Herbst) argument of Martin's Lemma 3.1.

Nothing here depends on the LPP model: these are facts about finite sums of real numbers.

## References

- J. B. Martin, *Limiting shape for directed percolation models*, Ann. Probab. 32 (2004),
  Lemma 3.1.
-/

@[expose] public section

namespace ProbabilityBasics.Concentration

section MaxOfSums

variable {ι : Type*} [DecidableEq ι]

/-- Sum of the drops `y j - update y i (-L) j` over a finite set `c`. Only the coordinate `i`
changes, so the sum is `y i + L` when `i ∈ c` and `0` otherwise. -/
private theorem sum_sub_update_neg (c : Finset ι) (y : ι → ℝ) (i : ι) (L : ℝ) :
    ∑ j ∈ c, (y j - Function.update y i (-L) j) = if i ∈ c then y i + L else 0 := by
  have hterm : ∀ j, y j - Function.update y i (-L) j = if i = j then y i + L else 0 := by
    intro j
    by_cases hij : i = j
    · subst hij
      simp [sub_neg_eq_add]
    · simp [Function.update_of_ne (Ne.symm hij), hij]
  rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_ite_eq]

/-- Lowering one coordinate to `-L` does not increase the maximum of the set sums (first fact for
Lemma 3.1 of Martin (2004)). Each set sum changes by `y i + L ≥ 0` or by `0`, because `y i ≥ -L`. -/
theorem sup_sum_update_neg_le (C : Finset (Finset ι)) (hC : C.Nonempty) {L : ℝ} {y : ι → ℝ}
    (hy : ∀ j, |y j| ≤ L) (i : ι) :
    C.sup' hC (fun c => ∑ j ∈ c, Function.update y i (-L) j) ≤
      C.sup' hC (fun c => ∑ j ∈ c, y j) := by
  refine Finset.sup'_le hC _ (fun c hc => ?_)
  -- The drop over `c` is `y i + L` or `0`; both are nonnegative since `-L ≤ y i`.
  have hnonneg : 0 ≤ if i ∈ c then y i + L else 0 := by
    split_ifs
    · linarith [(abs_le.1 (hy i)).1]
    · exact le_rfl
  have hdrop : 0 ≤ ∑ j ∈ c, (y j - Function.update y i (-L) j) := by
    rw [sum_sub_update_neg]
    exact hnonneg
  rw [Finset.sum_sub_distrib] at hdrop
  calc ∑ j ∈ c, Function.update y i (-L) j ≤ ∑ j ∈ c, y j := by linarith
    _ ≤ C.sup' hC (fun c => ∑ j ∈ c, y j) := Finset.le_sup' (fun c => ∑ j ∈ c, y j) hc

/-- A maximizing set controls every one-coordinate drop of the maximum (second fact for Lemma 3.1
of Martin (2004)). Let `c` attain the maximum at `y`. Lowering coordinate `i` to `-L` drops the
maximum by at most `2 L` when `i ∈ c`, and by at most `0` when `i ∉ c`. -/
theorem exists_mem_sup_sum_sub_update_neg_le (C : Finset (Finset ι)) (hC : C.Nonempty)
    {L : ℝ} {y : ι → ℝ} (hy : ∀ j, |y j| ≤ L) :
    ∃ c ∈ C, ∀ i, C.sup' hC (fun c => ∑ j ∈ c, y j) -
        C.sup' hC (fun c => ∑ j ∈ c, Function.update y i (-L) j) ≤
      if i ∈ c then 2 * L else 0 := by
  -- Take a set `c` that attains the maximum at `y`.
  obtain ⟨c, hcC, hceq⟩ := Finset.exists_mem_eq_sup' hC (fun c => ∑ j ∈ c, y j)
  have hZ : C.sup' hC (fun c => ∑ j ∈ c, y j) = ∑ j ∈ c, y j := hceq
  refine ⟨c, hcC, fun i => ?_⟩
  -- The maximum after lowering `i` is at least the sum over `c` of the lowered vector.
  have hle : ∑ j ∈ c, Function.update y i (-L) j ≤
      C.sup' hC (fun c => ∑ j ∈ c, Function.update y i (-L) j) :=
    Finset.le_sup' (fun c => ∑ j ∈ c, Function.update y i (-L) j) hcC
  have hdrop := sum_sub_update_neg c y i L
  rw [Finset.sum_sub_distrib] at hdrop
  rw [hZ]
  split_ifs at hdrop ⊢ with hi
  · linarith [(abs_le.1 (hy i)).2]
  · linarith

/-- Exponential estimate on the unit interval: `e^a - a - 1 ≤ a ^ 2` when `|a| ≤ 1`. This is
Mathlib's `Real.abs_exp_sub_one_sub_id_le`, weakened to the one-sided form used here. -/
private theorem exp_sub_sub_one_le_sq {a : ℝ} (ha : |a| ≤ 1) :
    Real.exp a - a - 1 ≤ a ^ 2 := by
  have h1 := le_abs_self (Real.exp a - 1 - a)
  have h2 := Real.abs_exp_sub_one_sub_id_le ha
  linarith

/-- For `0 ≤ d ≤ 2 L` and `2 L s ≤ 1` with `0 ≤ s`, the number `s d` lies in `[0, 1]` and its
square is at most `4 s² L²`. -/
private theorem abs_and_sq_mul_le {s L d : ℝ} (hs : 0 ≤ s) (hd0 : 0 ≤ d) (hd : d ≤ 2 * L)
    (hsL : 2 * L * s ≤ 1) : |s * d| ≤ 1 ∧ (s * d) ^ 2 ≤ 4 * s ^ 2 * L ^ 2 := by
  have hsd : s * d ≤ 1 := by
    linarith [mul_le_mul_of_nonneg_left hd hs]
  have hsq : d ^ 2 ≤ (2 * L) ^ 2 := pow_le_pow_left₀ hd0 hd 2
  refine ⟨?_, ?_⟩
  · rw [abs_of_nonneg (mul_nonneg hs hd0)]
    exact hsd
  · calc (s * d) ^ 2 = s ^ 2 * d ^ 2 := by ring
      _ ≤ s ^ 2 * (2 * L) ^ 2 := mul_le_mul_of_nonneg_left hsq (sq_nonneg s)
      _ = 4 * s ^ 2 * L ^ 2 := by ring

/-- A sum of terms, each at most `K` on the set `c` and at most `0` off `c`, is at most `R K`
when `|c| ≤ R`. -/
private theorem sum_le_card_mul [Fintype ι] {c : Finset ι} {R : ℕ} {K : ℝ}
    (hc : c.card ≤ R) (hK : 0 ≤ K) {f : ι → ℝ} (hf : ∀ i, f i ≤ if i ∈ c then K else 0) :
    ∑ i, f i ≤ (R : ℝ) * K := by
  calc ∑ i, f i ≤ ∑ i, (if i ∈ c then K else 0) := Finset.sum_le_sum fun i _ => hf i
    _ = (c.card : ℝ) * K := by simp [Finset.sum_ite_mem]
    _ ≤ (R : ℝ) * K := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hK

/-- Lower-tail exponential sum. Let `0 ≤ D i ≤ 2 L` for `i ∈ c`, `D i = 0`
off `c`, and `|c| ≤ R`. If `s ≥ 0` and `2 L s ≤ 1`, then the sum of `e^{s D i} - s D i - 1` over
all `i` is at most `4 s² L² R`. Uses Mathlib's `Real.abs_exp_sub_one_sub_id_le`. -/
theorem sum_exp_mul_sub_sub_one_le [Fintype ι] {D : ι → ℝ} {c : Finset ι} {L s : ℝ}
    {R : ℕ} (hc : c.card ≤ R) (hD0 : ∀ i, 0 ≤ D i)
    (hD : ∀ i, D i ≤ if i ∈ c then 2 * L else 0) (hs : 0 ≤ s) (hsL : 2 * L * s ≤ 1) :
    ∑ i, (Real.exp (s * D i) - s * D i - 1) ≤ 4 * s ^ 2 * L ^ 2 * R := by
  have hterm : ∀ i, Real.exp (s * D i) - s * D i - 1 ≤
      if i ∈ c then 4 * s ^ 2 * L ^ 2 else 0 := by
    intro i
    by_cases hi : i ∈ c
    · have h1 : D i ≤ 2 * L := by simpa [hi] using hD i
      obtain ⟨habs, hsq⟩ := abs_and_sq_mul_le hs (hD0 i) h1 hsL
      have hexp := exp_sub_sub_one_le_sq habs
      rw [ite_eq_left hi]
      linarith
    · have hD' : D i = 0 := le_antisymm (by simpa [hi] using hD i) (hD0 i)
      rw [ite_eq_right hi, hD', mul_zero, Real.exp_zero]
      norm_num
  have hsum := sum_le_card_mul hc (by positivity) hterm
  linarith

/-- Companion exponential sum for the sign `-s D i`. Under
the same hypotheses as `sum_exp_mul_sub_sub_one_le`, the sum of `e^{-s D i} + s D i - 1` over all
`i` is at most `4 s² L² R`. This is the weaker constant that the entropy argument needs, for
`s ≤ 1 / (2 L)`. -/
theorem sum_exp_neg_mul_add_sub_one_le [Fintype ι] {D : ι → ℝ} {c : Finset ι} {L s : ℝ}
    {R : ℕ} (hc : c.card ≤ R) (hD0 : ∀ i, 0 ≤ D i)
    (hD : ∀ i, D i ≤ if i ∈ c then 2 * L else 0) (hs : 0 ≤ s) (hsL : 2 * L * s ≤ 1) :
    ∑ i, (Real.exp (-(s * D i)) + s * D i - 1) ≤ 4 * s ^ 2 * L ^ 2 * R := by
  have hterm : ∀ i, Real.exp (-(s * D i)) + s * D i - 1 ≤
      if i ∈ c then 4 * s ^ 2 * L ^ 2 else 0 := by
    intro i
    by_cases hi : i ∈ c
    · have h1 : D i ≤ 2 * L := by simpa [hi] using hD i
      obtain ⟨habs, hsq⟩ := abs_and_sq_mul_le hs (hD0 i) h1 hsL
      have hexp := exp_sub_sub_one_le_sq (a := -(s * D i)) (by rw [abs_neg]; exact habs)
      rw [neg_sq] at hexp
      rw [ite_eq_left hi]
      linarith
    · have hD' : D i = 0 := le_antisymm (by simpa [hi] using hD i) (hD0 i)
      rw [ite_eq_right hi, hD', mul_zero, neg_zero, Real.exp_zero]
      norm_num
  have hsum := sum_le_card_mul hc (by positivity) hterm
  linarith

end MaxOfSums

end ProbabilityBasics.Concentration
