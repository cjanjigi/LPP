/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Frozen.Foundations.BK.BernoulliProduct
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic

/-! # Leading ones: laws on a finite chain from independent bits

This goes beyond van den Berg and Kesten (1985), which treats only bits and laws of
new-better-than-used type.

For bits `b : Fin k → Bool`, `leadingOnes b : Fin (k + 1)` is the number of leading
ones. It is increasing, and every probability law on `Fin (k + 1)` is the image of
independent bits (with their own probabilities) under `leadingOnes`. The bits have the
law `bernoulliProduct p` of `Frozen/Foundations/BK/BernoulliProduct.lean`.

## Main results

* `leadingOnes`: the number of `t` with `b s = true` for all `s ≤ t`.
* `monotone_leadingOnes`: `leadingOnes` is increasing for the pointwise order.
* `exists_bernoulli_leadingOnes`: every probability law on `Fin (k + 1)` is the image of
  some `bernoulliProduct p` under `leadingOnes`.

## Proof outline

With `S j = ν {i | j ≤ i}` and `q t = S (t + 1) / S t` (`0` when `S t = 0`), the event
"at least `j` leading ones" is the box "the first `j` bits are `1`". Its probability is
`∏_{t < j} q t = S j` by telescoping. Singletons then have the right mass.

## References

- J. van den Berg and H. Kesten, *Inequalities with applications to percolation and reliability*,
  J. Appl. Probab. 22 (1985).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace ProbabilityBasics.BK

variable {k : ℕ}

/-- The number of leading ones of the bits `b`: the number of positions `t` such that
`b s = true` for every `s ≤ t`. It is at most `k`, so it lies in `Fin (k + 1)`. -/
def leadingOnes (b : Fin k → Bool) : Fin (k + 1) :=
  ⟨(univ.filter fun t : Fin k => ∀ s, s ≤ t → b s = true).card,
    Nat.lt_succ_of_le ((Finset.card_filter_le _ _).trans_eq (by simp))⟩

private lemma leadingOnes_val (b : Fin k → Bool) :
    (leadingOnes b).val = (univ.filter fun t : Fin k => ∀ s, s ≤ t → b s = true).card :=
  rfl

/-- Adding ones to the bits cannot decrease the number of leading ones. -/
theorem monotone_leadingOnes : Monotone (leadingOnes : (Fin k → Bool) → Fin (k + 1)) := by
  intro b b' hbb'
  rw [Fin.le_def, leadingOnes_val, leadingOnes_val]
  apply Finset.card_le_card
  intro t ht
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
  intro s hs
  by_contra hne
  have hf : b' s = false := by simpa using hne
  have h := hbb' s
  rw [ht s hs, hf] at h
  exact absurd (Bool.le_iff_imp.mp h rfl) (by simp)

/-- At least `j` leading ones means the first `j` bits are all `true` (for `j ≤ k`). -/
private lemma le_leadingOnes_iff (b : Fin k → Bool) (j : ℕ) (hj : j ≤ k) :
    j ≤ (leadingOnes b).val ↔ ∀ t : Fin k, t.val < j → b t = true := by
  rw [leadingOnes_val]
  constructor
  · intro hcard t htj
    by_contra hbt
    have hsub : (univ.filter fun t : Fin k => ∀ s, s ≤ t → b s = true) ⊆ Finset.Iio t := by
      intro s hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
      rw [Finset.mem_Iio]
      by_contra hst
      exact hbt (hs t (not_lt.mp hst))
    have h1 := Finset.card_le_card hsub
    rw [Fin.card_Iio] at h1
    omega
  · intro h
    have hsub : (univ.filter fun t : Fin k => (t : ℕ) < j) ⊆
        univ.filter fun t : Fin k => ∀ s, s ≤ t → b s = true := by
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      intro s hs
      exact h s (lt_of_le_of_lt hs ht)
    have h1 := Finset.card_le_card hsub
    rw [Fin.card_filter_val_lt] at h1
    omega

/-- The tail masses `S j = ν {i | j ≤ i}` of a law on `Fin (k + 1)`. -/
private noncomputable def tail (ν : Measure (Fin (k + 1))) (j : ℕ) : ℝ≥0∞ :=
  ν {i : Fin (k + 1) | j ≤ i.val}

/-- The conditional probabilities `q t = S (t + 1) / S t`, and `0` when `S t = 0`. -/
private noncomputable def stepProb (ν : Measure (Fin (k + 1))) (t : ℕ) : ℝ≥0∞ :=
  if tail ν t = 0 then 0 else tail ν (t + 1) / tail ν t

private lemma tail_antitone (ν : Measure (Fin (k + 1))) : Antitone (tail ν) :=
  fun _ _ hij => measure_mono fun _ hx => le_trans hij hx

private lemma tail_zero (ν : Measure (Fin (k + 1))) [IsProbabilityMeasure ν] :
    tail ν 0 = 1 := by
  simp [tail]

private lemma tail_last (ν : Measure (Fin (k + 1))) : tail ν (k + 1) = 0 := by
  have : {i : Fin (k + 1) | k + 1 ≤ i.val} = ∅ :=
    Set.eq_empty_iff_forall_notMem.2 fun i hi => absurd hi (not_le.2 i.isLt)
  rw [tail, this, measure_empty]

private lemma tail_le_one (ν : Measure (Fin (k + 1))) [IsProbabilityMeasure ν] (j : ℕ) :
    tail ν j ≤ 1 :=
  prob_le_one

private lemma tail_ne_top (ν : Measure (Fin (k + 1))) [IsProbabilityMeasure ν] (j : ℕ) :
    tail ν j ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (tail_le_one ν j)

/-- The mass at `j` is the drop from `S j` to `S (j + 1)`. -/
private lemma tail_eq_add (ν : Measure (Fin (k + 1))) (j : Fin (k + 1)) :
    tail ν j.val = ν {j} + tail ν (j.val + 1) := by
  have hset : {i : Fin (k + 1) | j.val ≤ i.val} =
      {j} ∪ {i : Fin (k + 1) | j.val + 1 ≤ i.val} := by
    ext i
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · intro h
      rcases h.eq_or_lt with h | h
      · exact Or.inl (Fin.ext h.symm)
      · exact Or.inr h
    · rintro (h | h)
      · rw [h]
      · exact le_trans (Nat.le_succ _) h
  have hdisj : Disjoint ({j} : Set (Fin (k + 1)))
      {i : Fin (k + 1) | j.val + 1 ≤ i.val} := by
    rw [Set.disjoint_singleton_left]
    simp
  rw [tail, hset, measure_union hdisj (MeasurableSet.of_discrete)]
  rfl

private lemma stepProb_le_one (ν : Measure (Fin (k + 1))) (t : ℕ) : stepProb ν t ≤ 1 := by
  unfold stepProb
  split_ifs with h
  · exact zero_le
  · exact ENNReal.div_le_of_le_mul (by simpa using tail_antitone ν (Nat.le_succ t))

/-- Telescoping: the product of the first `j` conditional probabilities is `S j`. -/
private lemma prod_range_stepProb (ν : Measure (Fin (k + 1))) [IsProbabilityMeasure ν]
    (j : ℕ) : ∏ t ∈ range j, stepProb ν t = tail ν j := by
  induction j with
  | zero => simp [tail_zero]
  | succ j ih =>
    rw [Finset.prod_range_succ, ih]
    unfold stepProb
    split_ifs with h
    · rw [mul_zero]
      exact (le_antisymm (h ▸ tail_antitone ν (Nat.le_succ j)) zero_le).symm
    · exact ENNReal.mul_div_cancel h (tail_ne_top ν j)

/-- The probabilities of the bits that realise a given law, as points of `[0, 1]`. -/
private noncomputable def bitProb (ν : Measure (Fin (k + 1))) (t : Fin k) : unitInterval :=
  ⟨(stepProb ν t).toReal, ENNReal.toReal_nonneg, by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (stepProb_le_one ν t)⟩

private lemma coe_toNNReal_bitProb (ν : Measure (Fin (k + 1))) [IsProbabilityMeasure ν]
    (t : Fin k) : ((unitInterval.toNNReal (bitProb ν t) : NNReal) : ℝ≥0∞) = stepProb ν t := by
  have hne : stepProb ν t ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (stepProb_le_one ν t)
  rw [ENNReal.coe_nnreal_eq]
  simp only [unitInterval.toNNReal, bitProb]
  exact ENNReal.ofReal_toReal hne

/-- The event "at least `j` leading ones" is the box "the first `j` bits are `true`". -/
private lemma le_leadingOnes_eq_pi (j : ℕ) (hj : j ≤ k) :
    {b : Fin k → Bool | j ≤ (leadingOnes b).val} =
      Set.pi Set.univ fun t : Fin k => if (t : ℕ) < j then ({true} : Set Bool) else Set.univ := by
  ext b
  simp only [Set.mem_ofPred_eq, le_leadingOnes_iff b j hj, Set.mem_pi, Set.mem_univ,
    true_implies]
  refine forall_congr' fun t => ?_
  by_cases ht : (t : ℕ) < j <;> simp [ht]

/-- The probability of "at least `j` leading ones" is `S j`, for `j ≤ k`. -/
private lemma measure_le_leadingOnes (ν : Measure (Fin (k + 1))) [IsProbabilityMeasure ν]
    (j : ℕ) (hj : j ≤ k) :
    bernoulliProduct (bitProb ν) {b | j ≤ (leadingOnes b).val} = tail ν j := by
  rw [le_leadingOnes_eq_pi j hj, bernoulliProduct, Measure.pi_pi]
  have hfac : ∀ t : Fin k,
      bernoulliMeasure true false (bitProb ν t)
          (if (t : ℕ) < j then ({true} : Set Bool) else Set.univ) =
        if (t : ℕ) < j then stepProb ν t else 1 := by
    intro t
    by_cases ht : (t : ℕ) < j
    · simp only [ht, ↓reduceIte]
      rw [bernoulliMeasure_apply_of_mem_of_notMem _ (MeasurableSet.of_discrete)
        (Set.mem_singleton true) (by simp)]
      exact coe_toNNReal_bitProb ν t
    · simp [ht]
  simp only [hfac]
  rw [← prod_range_stepProb ν j]
  refine (Fin.prod_univ_eq_prod_range (fun i => if i < j then stepProb ν i else 1) k).trans ?_
  have hfil : (range k).filter (fun i => i < j) = range j := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [← Finset.prod_filter, hfil]

/-- `leadingOnes` is measurable, since the space of bits is discrete. -/
private lemma measurable_leadingOnes : Measurable (leadingOnes : (Fin k → Bool) → Fin (k + 1)) :=
  Measurable.of_discrete

/-- Every probability law on `Fin (k + 1)` is the image of independent bits under
`leadingOnes`. The bit at position `t` is `true` with probability `S (t + 1) / S t`, where
`S j = ν {i | j ≤ i}` (and `0` when `S t = 0`). -/
theorem exists_bernoulli_leadingOnes (ν : Measure (Fin (k + 1))) [IsProbabilityMeasure ν] :
    ∃ p : Fin k → unitInterval, (bernoulliProduct p).map leadingOnes = ν := by
  refine ⟨bitProb ν, Measure.ext_of_singleton fun a => ?_⟩
  set μ := bernoulliProduct (bitProb ν) with hμ
  -- the mass of "at least `j` leading ones", also for `j = k + 1`
  have hlevel : ∀ j : ℕ, j ≤ k + 1 → μ {b | j ≤ (leadingOnes b).val} = tail ν j := by
    intro j hj
    rcases hj.eq_or_lt with rfl | hlt
    · have : {b : Fin k → Bool | k + 1 ≤ (leadingOnes b).val} = ∅ := by
        ext b
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
        exact (leadingOnes b).isLt
      rw [this, tail_last, measure_empty]
    · exact measure_le_leadingOnes ν j (Nat.lt_succ_iff.mp hlt)
  have hfiber : leadingOnes ⁻¹' {a} =
      {b : Fin k → Bool | a.val ≤ (leadingOnes b).val} \
        {b | a.val + 1 ≤ (leadingOnes b).val} := by
    ext b
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_sdiff, Set.mem_ofPred_eq,
      not_le, Nat.lt_succ_iff, Fin.ext_iff]
    omega
  have hsub : {b : Fin k → Bool | a.val + 1 ≤ (leadingOnes b).val} ⊆
      {b | a.val ≤ (leadingOnes b).val} := fun b hb => le_trans (Nat.le_succ _) hb
  have hsucc : μ {b | a.val + 1 ≤ (leadingOnes b).val} = tail ν (a.val + 1) :=
    hlevel _ (Nat.succ_le_of_lt a.isLt)
  rw [Measure.map_apply measurable_leadingOnes (MeasurableSet.of_discrete), hfiber,
    measure_sdiff hsub (MeasurableSet.of_discrete).nullMeasurableSet
      (by rw [hsucc]; exact tail_ne_top ν _),
    hlevel _ (by have := a.isLt; omega), hsucc, tail_eq_add ν a,
    ENNReal.add_sub_cancel_right (tail_ne_top ν _)]

end ProbabilityBasics.BK
