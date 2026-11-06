/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Analysis.BinomialStirlingEntropy
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

import Mathlib.Tactic.Ring

/-! # Entropy tails and the first Borel–Cantelli lemma

If event probabilities have a binomial entropy bound with a strict exponent
gap, the probabilities are summable and the first Borel–Cantelli lemma applies.
The event bound remains an explicit premise; this module does not construct a
passage event or prove its tail estimate.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal

namespace LPPDifferentiability

/-- The real probabilities are summable under a strict binomial entropy gap.
The bound is required only for positive indices, so the arbitrary finite
prefix, including index zero, is handled separately. -/
theorem summable_real_measure_of_entropy_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (a b : ℕ) {c : ℝ}
    (hc : (((a + b : ℕ) : ℝ) * Real.log (a + b : ℕ) -
        (a : ℝ) * Real.log a - (b : ℝ) * Real.log b) < c)
    (A : ℕ → Set Ω)
    (hTail : ∀ n : ℕ, 0 < n → μ.real (A n) ≤
      ((n * (a + b)).choose (n * a) : ℝ) * Real.exp (64 - (n : ℝ) * c)) :
    Summable (fun n : ℕ => μ.real (A n)) := by
  let δ : ℝ := (c - (((a + b : ℕ) : ℝ) * Real.log (a + b : ℕ) -
    (a : ℝ) * Real.log a - (b : ℝ) * Real.log b)) / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith
  have hchoose := eventually_log_choose_mul_le a b hδ
  have hbound : ∀ᶠ n : ℕ in atTop,
      ‖μ.real (A n)‖ ≤ Real.exp 64 * Real.exp ((n : ℝ) * (-δ)) := by
    filter_upwards [hchoose, eventually_gt_atTop (0 : ℕ)] with n hchoose hn
    have hchooseIndex : n * a ≤ n * (a + b) :=
      Nat.mul_le_mul_left n (Nat.le_add_right a b)
    have hchoosePos : (0 : ℝ) < ((n * (a + b)).choose (n * a) : ℝ) := by
      exact_mod_cast Nat.choose_pos hchooseIndex
    have hchooseExp : ((n * (a + b)).choose (n * a) : ℝ) ≤
        Real.exp ((n : ℝ) * ((((a + b : ℕ) : ℝ) * Real.log (a + b : ℕ) -
          (a : ℝ) * Real.log a - (b : ℝ) * Real.log b) + δ)) := by
      calc
        _ = Real.exp (Real.log ((n * (a + b)).choose (n * a) : ℝ)) :=
          (Real.exp_log hchoosePos).symm
        _ ≤ _ := Real.exp_le_exp.mpr hchoose
    calc
      ‖μ.real (A n)‖ = μ.real (A n) := Real.norm_of_nonneg measureReal_nonneg
      _ ≤ ((n * (a + b)).choose (n * a) : ℝ) * Real.exp (64 - (n : ℝ) * c) :=
        hTail n hn
      _ ≤ Real.exp ((n : ℝ) * ((((a + b : ℕ) : ℝ) * Real.log (a + b : ℕ) -
          (a : ℝ) * Real.log a - (b : ℝ) * Real.log b) + δ)) *
          Real.exp (64 - (n : ℝ) * c) :=
        mul_le_mul_of_nonneg_right hchooseExp (Real.exp_nonneg _)
      _ = Real.exp 64 * Real.exp ((n : ℝ) * (-δ)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        dsimp [δ]
        ring
  obtain ⟨N, hN⟩ := eventually_atTop.1 hbound
  have hgeom : Summable (fun n : ℕ =>
      Real.exp 64 * Real.exp ((n : ℝ) * (-δ))) := by
    exact (Real.summable_exp_nat_mul_iff.mpr (neg_lt_zero.mpr hδ)).mul_left
      (Real.exp 64)
  have hprefix : Summable (fun n : ℕ => if n < N then (1 : ℝ) else 0) := by
    apply summable_of_hasFiniteSupport
    refine Set.finite_Iio N |>.subset ?_
    intro n hn
    change (if n < N then (1 : ℝ) else 0) ≠ 0 at hn
    by_contra hnlt
    have hnlt' : ¬ n < N := by simpa only [Set.mem_Iio] using hnlt
    have hnN : N ≤ n := Nat.le_of_not_gt hnlt'
    have hzero : (if n < N then (1 : ℝ) else 0) = 0 := by
      simp [Nat.not_lt.mpr hnN]
    exact hn hzero
  have htail : Summable (fun n : ℕ =>
      if N ≤ n then Real.exp 64 * Real.exp ((n : ℝ) * (-δ)) else 0) := by
    refine Summable.of_nonneg_of_le ?_ ?_ hgeom
    · intro n
      by_cases hn : N ≤ n
      · simpa [hn] using mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)
      · simp [hn]
    · intro n
      by_cases hn : N ≤ n
      · simp [hn]
      · simp [hn]
        exact mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)
  let envelope : ℕ → ℝ := fun n =>
    if n < N then 1 else Real.exp 64 * Real.exp ((n : ℝ) * (-δ))
  have henvelope : Summable envelope := by
    have heq : envelope = fun n : ℕ =>
        (if n < N then (1 : ℝ) else 0) +
          (if N ≤ n then Real.exp 64 * Real.exp ((n : ℝ) * (-δ)) else 0) := by
      funext n
      by_cases hn : n < N
      · have hnot : ¬ N ≤ n := by omega
        simp [envelope, hn, hnot]
      · have hge : N ≤ n := by omega
        simp [envelope, hn, hge]
    rw [heq]
    exact hprefix.add htail
  have hmeasureLe (n : ℕ) : μ.real (A n) ≤ envelope n := by
    by_cases hn : n < N
    · simp [envelope, hn]
    · have hnN : N ≤ n := Nat.le_of_not_gt hn
      have hlarge := hN n hnN
      rw [Real.norm_of_nonneg measureReal_nonneg] at hlarge
      simpa [envelope, hn] using hlarge
  exact Summable.of_nonneg_of_le (fun n => measureReal_nonneg) hmeasureLe henvelope

/-- The sum of the ENNReal event measures is finite under the same strict
entropy gap. Probability finiteness justifies each real to ENNReal conversion. -/
theorem tsum_measure_ne_top_of_entropy_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (a b : ℕ) {c : ℝ}
    (hc : (((a + b : ℕ) : ℝ) * Real.log (a + b : ℕ) -
        (a : ℝ) * Real.log a - (b : ℝ) * Real.log b) < c)
    (A : ℕ → Set Ω)
    (hTail : ∀ n : ℕ, 0 < n → μ.real (A n) ≤
      ((n * (a + b)).choose (n * a) : ℝ) * Real.exp (64 - (n : ℝ) * c)) :
    (∑' n : ℕ, μ (A n)) ≠ ∞ := by
  have hreal := summable_real_measure_of_entropy_tail μ a b hc A hTail
  have hfinite (n : ℕ) : μ (A n) ≠ ∞ := by
    apply ne_of_lt
    exact (prob_le_one (μ := μ) (s := A n)).trans_lt ENNReal.one_lt_top
  calc
    (∑' n : ℕ, μ (A n)) = ∑' n : ℕ, ENNReal.ofReal (μ.real (A n)) := by
      apply tsum_congr
      intro n
      exact (ofReal_measureReal (hfinite n)).symm
    _ = ENNReal.ofReal (∑' n : ℕ, μ.real (A n)) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun n => measureReal_nonneg) hreal).symm
    _ ≠ ∞ := ENNReal.ofReal_ne_top

/-- Almost surely, only finitely many events occur under a strict entropy gap.
The conclusion uses the first Borel–Cantelli lemma and assumes no independence. -/
theorem ae_eventually_notMem_of_entropy_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (a b : ℕ) {c : ℝ}
    (hc : (((a + b : ℕ) : ℝ) * Real.log (a + b : ℕ) -
        (a : ℝ) * Real.log a - (b : ℝ) * Real.log b) < c)
    (A : ℕ → Set Ω)
    (hTail : ∀ n : ℕ, 0 < n → μ.real (A n) ≤
      ((n * (a + b)).choose (n * a) : ℝ) * Real.exp (64 - (n : ℝ) * c)) :
    ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, ω ∉ A n := by
  exact MeasureTheory.ae_eventually_notMem
    (tsum_measure_ne_top_of_entropy_tail μ a b hc A hTail)

/-- Zero-axis event bounds are summable whenever their exponential rate is
positive. The event at index zero is unrestricted. -/
theorem ae_eventually_notMem_of_zeroAxis_exp_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (a b : ℕ)
    (hAxis : a = 0 ∨ b = 0) {c : ℝ} (hc : 0 < c) (A : ℕ → Set Ω)
    (hTail : ∀ n : ℕ, 0 < n → μ.real (A n) ≤ Real.exp (64 - (n : ℝ) * c)) :
    ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, ω ∉ A n := by
  have hEntropy : (((a + b : ℕ) : ℝ) * Real.log (a + b : ℕ) -
      (a : ℝ) * Real.log a - (b : ℝ) * Real.log b) = 0 := by
    rcases hAxis with ha | hb
    · simp [ha]
    · simp [hb]
  have hgap : (((a + b : ℕ) : ℝ) * Real.log (a + b : ℕ) -
      (a : ℝ) * Real.log a - (b : ℝ) * Real.log b) < c := by
    rw [hEntropy]
    exact hc
  apply ae_eventually_notMem_of_entropy_tail μ a b hgap A
  intro n hn
  have hchoose : ((n * (a + b)).choose (n * a) : ℝ) = 1 := by
    rcases hAxis with ha | hb
    · simp [ha]
    · simp [hb]
  simpa [hchoose] using hTail n hn

end LPPDifferentiability
