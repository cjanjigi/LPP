/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Analysis.PositiveQuadrantDensity
public import ProbabilityBasics.Analysis.PositiveSubadditiveRate
public import Martin2004.Analysis.RationalPassageNormalization
public import LPP_Foundations.Probability.PassageLaw
public import LPP_Foundations.Probability.PassageMeanMonotone

import Mathlib.Tactic

/-!
# The expected floor rate as an EReal limit

Fix a weight law `μ` with finite mean `m`, and a nonnegative real direction `x`.
The expected last-passage time `E T(⌊n x⌋)` divided by `n` converges in `EReal`
to a limit `g x` with values in `(-∞, +∞]`.

The proof uses the corrected means `a n = E T(⌊n x⌋) - m (⌊n x₁⌋ + ⌊n x₂⌋)`.
These are superadditive in `n` (the corrected mean is monotone in the endpoint,
and expected passage is superadditive). An `EReal` version of Fekete's lemma then
gives the limit of `a n / n`, and adding back the linear term `m (x₁ + x₂)` gives
the limit of `E T(⌊n x⌋) / n`. The bounded case of Fekete's lemma is
`exists_positive_subadditive_rate`; the unbounded case (limit `+∞`) is proved here.

Definition (2.3) and the introduction of Martin (2004) describe the rate as a
supremum and state that it is a limit. Proposition 2.1(i) states the
almost-sure passage-time limit under a finite first moment. This file proves
the expected floor-rate limit in `EReal`, allowing `+∞`, by applying an
`EReal` form of Fekete's lemma to the corrected expected means above.
-/

public section

open MeasureTheory Filter Set
open scoped Topology NNReal

namespace LPPDifferentiability

/-- Fekete's lemma in `EReal`. For a real sequence `a` that is superadditive on
positive indices, the normalized values `a n / n` converge in `EReal` to a value `s`
that is their least upper bound over positive `n`. The value `s` is finite when
the sequence is bounded above and `+∞` otherwise. -/
theorem ereal_fekete_superadditive (a : ℕ → ℝ)
    (hsuper : ∀ m n : ℕ, 0 < m → 0 < n → a m + a n ≤ a (m + n)) :
    ∃ s : EReal,
      Tendsto (fun n : ℕ => ((a n / (n : ℝ) : ℝ) : EReal)) atTop (𝓝 s) ∧
      (∀ n : ℕ, 0 < n → ((a n / (n : ℝ) : ℝ) : EReal) ≤ s) ∧
      ∀ t : EReal, (∀ n : ℕ, 0 < n → ((a n / (n : ℝ) : ℝ) : EReal) ≤ t) → s ≤ t := by
  by_cases hbdd : BddAbove (range fun n : ℕ => a n / (n : ℝ))
  · -- Bounded case: apply the real Fekete lemma to `-a`.
    obtain ⟨S, hS⟩ := hbdd
    have hS' : ∀ n : ℕ, a n / (n : ℝ) ≤ S := fun n => hS ⟨n, rfl⟩
    have hdiv : ∀ n : ℕ, 0 < n → a n ≤ S * (n : ℝ) := fun n hn =>
      (div_le_iff₀ (Nat.cast_pos.mpr hn)).mp (hS' n)
    obtain ⟨γ, hγlim, hγinf⟩ := exists_positive_subadditive_rate (fun n => -a n)
      (fun m n hm hn => by
        have := hsuper m n hm hn
        show -a (m + n) ≤ -a m + -a n
        linarith)
      (-S) (fun n hn => by
        have := hdiv n hn
        show -S * (n : ℝ) ≤ -a n
        linarith)
    have hkey : ∀ k : ℕ, γ ≤ -a (k + 1) / ((k + 1 : ℕ) : ℝ) := by
      intro k
      rw [hγinf]
      apply csInf_le
      · refine ⟨-S, ?_⟩
        rintro _ ⟨j, rfl⟩
        show -S ≤ -a (j + 1) / ((j + 1 : ℕ) : ℝ)
        have hj : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
        rw [le_div_iff₀ hj]
        linarith [hdiv (j + 1) (Nat.succ_pos j)]
      · exact ⟨k, rfl⟩
    refine ⟨((-γ : ℝ) : EReal), ?_, ?_, ?_⟩
    · have h1 : Tendsto (fun n : ℕ => a (n + 1) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 (-γ)) := by
        have h2 : Tendsto (fun n : ℕ => -(-a (n + 1) / ((n + 1 : ℕ) : ℝ))) atTop
            (𝓝 (-γ)) := hγlim.neg
        refine Tendsto.congr (fun n => ?_) h2
        simp only [neg_div, neg_neg]
      have h3 : Tendsto (fun n : ℕ => ((a (n + 1) / ((n + 1 : ℕ) : ℝ) : ℝ) : EReal))
          atTop (𝓝 ((-γ : ℝ) : EReal)) :=
        EReal.tendsto_coe.mpr h1
      exact (tendsto_add_atTop_iff_nat 1).mp h3
    · intro n hn
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      have hk := hkey k
      rw [EReal.coe_le_coe_iff]
      have hneg : -a (k + 1) / ((k + 1 : ℕ) : ℝ) = -(a (k + 1) / ((k + 1 : ℕ) : ℝ)) :=
        neg_div _ _
      linarith
    · intro t ht
      induction t using EReal.rec with
      | bot => exact absurd (le_bot_iff.mp (ht 1 one_pos)) (EReal.coe_ne_bot _)
      | coe u =>
        have hu : ∀ n : ℕ, 0 < n → a n / (n : ℝ) ≤ u := fun n hn =>
          EReal.coe_le_coe_iff.mp (ht n hn)
        have hlb : -u ≤ γ := by
          rw [hγinf]
          apply le_csInf (Set.range_nonempty _)
          rintro _ ⟨j, rfl⟩
          have h := hu (j + 1) (Nat.succ_pos j)
          show -u ≤ -a (j + 1) / ((j + 1 : ℕ) : ℝ)
          rw [neg_div]
          linarith
        rw [EReal.coe_le_coe_iff]
        linarith
      | top => exact le_top
  · -- Unbounded case: the limit is `+∞`.
    rw [not_bddAbove_iff] at hbdd
    have key : ∀ K : ℝ, 0 ≤ K → ∀ᶠ n : ℕ in atTop, K < a n / (n : ℝ) := by
      intro K hK
      obtain ⟨y, ⟨N, rfl⟩, hNy⟩ := hbdd (K + 1)
      have hNy' : K + 1 < a N / (N : ℝ) := hNy
      have hN : 0 < N := by
        rcases Nat.eq_zero_or_pos N with h | h
        · subst h
          have h0 : a 0 / ((0 : ℕ) : ℝ) = 0 := by simp
          rw [h0] at hNy'
          linarith
        · exact h
      have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
      have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
      obtain ⟨c, hc⟩ : ∃ c : ℝ, c = a N / (N : ℝ) := ⟨_, rfl⟩
      have haN : a N = c * (N : ℝ) := by
        rw [hc]
        field_simp
      have hcgt : K + 1 < c := by
        rw [hc]
        exact hNy'
      have hcK : 0 < c - K := by linarith
      have hc0 : 0 ≤ c := by linarith
      obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ r : ℕ, N ≤ r → r < 2 * N → |a r| ≤ C :=
        ⟨∑ j ∈ Finset.Ico N (2 * N), |a j|, fun r h1 h2 =>
          Finset.single_le_sum (f := fun j => |a j|) (fun j _ => abs_nonneg (a j))
            (Finset.mem_Ico.mpr ⟨h1, h2⟩)⟩
      -- Multiples of `N`: `a ((k+1) N) ≥ (k+1) a N`.
      have hmul : ∀ k : ℕ, ((k : ℝ) + 1) * a N ≤ a ((k + 1) * N) := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          have h := hsuper ((k + 1) * N) N (Nat.mul_pos (Nat.succ_pos k) hN) hN
          have e : (k + 1 + 1) * N = (k + 1) * N + N := by ring
          rw [e]
          push_cast
          linarith
      obtain ⟨M, hM⟩ := exists_nat_gt ((2 * N * c + C) / (c - K))
      refine Filter.eventually_atTop.mpr ⟨max (2 * N) M, fun n hn => ?_⟩
      have h2N : 2 * N ≤ n := le_trans (le_max_left _ _) hn
      have hMn : M ≤ n := le_trans (le_max_right _ _) hn
      have hthr : 2 * (N : ℝ) * c + C < (n : ℝ) * (c - K) := by
        have h1 : (2 * N * c + C) / (c - K) < (n : ℝ) :=
          lt_of_lt_of_le hM (by exact_mod_cast hMn)
        exact (div_lt_iff₀ hcK).mp h1
      -- Write n = q N + r with q ≥ 1 and N ≤ r < 2 N.
      obtain ⟨q, r, hq, hnqr, hrN, hr2N⟩ :
          ∃ q r : ℕ, 1 ≤ q ∧ n = q * N + r ∧ N ≤ r ∧ r < 2 * N := by
        have h1 := Nat.div_add_mod n N
        have h2 : 2 ≤ n / N := (Nat.le_div_iff_mul_le hN).mpr (by omega)
        have h3 := Nat.mod_lt n hN
        generalize n / N = p at h1 h2
        generalize n % N = t at h1 h3
        obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
        exact ⟨p', t + N, by omega, (by rw [← h1]; ring), by omega, by omega⟩
      subst hnqr
      obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
      have hr_pos : 0 < r := by omega
      have hA : ((k : ℝ) + 1) * (c * (N : ℝ)) - C ≤ a ((k + 1) * N + r) := by
        have hsum := hsuper ((k + 1) * N) r (Nat.mul_pos (Nat.succ_pos k) hN) hr_pos
        have hm := hmul k
        have hCr := hC r hrN hr2N
        have hnegC : -C ≤ a r := by linarith [neg_abs_le (a r)]
        have hmulc : ((k : ℝ) + 1) * a N = ((k : ℝ) + 1) * (c * (N : ℝ)) := by
          rw [haN]
        linarith
      have hcast : (((k + 1) * N + r : ℕ) : ℝ) = ((k : ℝ) + 1) * (N : ℝ) + (r : ℝ) := by
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
      have hnc2 : (((k + 1) * N + r : ℕ) : ℝ) * c =
          ((k : ℝ) + 1) * (N : ℝ) * c + (r : ℝ) * c := by
        rw [hcast]
        ring
      have hrc : (r : ℝ) * c ≤ 2 * (N : ℝ) * c :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hr2N.le) hc0
      have hnpos : (0 : ℝ) < (((k + 1) * N + r : ℕ) : ℝ) := by
        have : 0 < (k + 1) * N + r := by
          have := Nat.mul_pos (Nat.succ_pos k) hN
          omega
        exact_mod_cast this
      rw [lt_div_iff₀ hnpos]
      linarith
    have hlim : Tendsto (fun n : ℕ => ((a n / (n : ℝ) : ℝ) : EReal)) atTop (𝓝 ⊤) := by
      rw [EReal.tendsto_nhds_top_iff_real]
      intro K
      filter_upwards [key (max K 0) (le_max_right K 0)] with n hn
      exact EReal.coe_lt_coe_iff.mpr (lt_of_le_of_lt (le_max_left K 0) hn)
    refine ⟨⊤, hlim, fun n _ => le_top, fun t ht => ?_⟩
    induction t using EReal.rec with
    | bot => exact absurd (le_bot_iff.mp (ht 1 one_pos)) (EReal.coe_ne_bot _)
    | top => exact le_rfl
    | coe u =>
      obtain ⟨y, ⟨n, rfl⟩, hy⟩ := hbdd (max u 0)
      have hn : 0 < n := by
        rcases Nat.eq_zero_or_pos n with h | h
        · subst h
          have h0 : a 0 / ((0 : ℕ) : ℝ) = 0 := by simp
          have hy' : max u 0 < a 0 / ((0 : ℕ) : ℝ) := hy
          rw [h0] at hy'
          linarith [le_max_right u 0]
        · exact h
      have hun : a n / (n : ℝ) ≤ u := EReal.coe_le_coe_iff.mp (ht n hn)
      have hy' : max u 0 < a n / (n : ℝ) := hy
      linarith [le_max_left u 0]

/-- Corrected expected passage values are superadditive in the index: the
two-index form of the corrected floor superadditivity. -/
private theorem corrected_floor_superadd_index
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ) (x : Quadrant) (k l : ℕ) :
    ((∫ ω : Environment, lastPassage ω 0
        (⌊(k : ℝ) * (x.1 : ℝ)⌋₊, ⌊(k : ℝ) * (x.2 : ℝ)⌋₊) ∂environmentLaw μ) -
      ((⌊(k : ℝ) * (x.1 : ℝ)⌋₊ + ⌊(k : ℝ) * (x.2 : ℝ)⌋₊ : ℕ) : ℝ) * (∫ t : ℝ, t ∂μ)) +
    ((∫ ω : Environment, lastPassage ω 0
        (⌊(l : ℝ) * (x.1 : ℝ)⌋₊, ⌊(l : ℝ) * (x.2 : ℝ)⌋₊) ∂environmentLaw μ) -
      ((⌊(l : ℝ) * (x.1 : ℝ)⌋₊ + ⌊(l : ℝ) * (x.2 : ℝ)⌋₊ : ℕ) : ℝ) * (∫ t : ℝ, t ∂μ)) ≤
    (∫ ω : Environment, lastPassage ω 0
        (⌊((k + l : ℕ) : ℝ) * (x.1 : ℝ)⌋₊, ⌊((k + l : ℕ) : ℝ) * (x.2 : ℝ)⌋₊)
          ∂environmentLaw μ) -
      ((⌊((k + l : ℕ) : ℝ) * (x.1 : ℝ)⌋₊ + ⌊((k + l : ℕ) : ℝ) * (x.2 : ℝ)⌋₊ : ℕ) : ℝ) *
        (∫ t : ℝ, t ∂μ) := by
  have hfl : ∀ u : ℝ, 0 ≤ u → ∀ p q : ℕ,
      ⌊(p : ℝ) * u⌋₊ + ⌊(q : ℝ) * u⌋₊ ≤ ⌊((p + q : ℕ) : ℝ) * u⌋₊ := by
    intro u hu p q
    apply Nat.le_floor
    have h1 := Nat.floor_le (mul_nonneg (Nat.cast_nonneg p) hu)
    have h2 := Nat.floor_le (mul_nonneg (Nat.cast_nonneg q) hu)
    push_cast
    linarith [add_mul (p : ℝ) (q : ℝ) u]
  have hsum1 : ⌊(k : ℝ) * (x.1 : ℝ)⌋₊ + ⌊(l : ℝ) * (x.1 : ℝ)⌋₊ ≤
      ⌊((k + l : ℕ) : ℝ) * (x.1 : ℝ)⌋₊ := hfl _ (NNReal.coe_nonneg _) k l
  have hsum2 : ⌊(k : ℝ) * (x.2 : ℝ)⌋₊ + ⌊(l : ℝ) * (x.2 : ℝ)⌋₊ ≤
      ⌊((k + l : ℕ) : ℝ) * (x.2 : ℝ)⌋₊ := hfl _ (NNReal.coe_nonneg _) k l
  have hs := integral_lastPassage_superadditive μ hμ 0
    (⌊(k : ℝ) * (x.1 : ℝ)⌋₊, ⌊(k : ℝ) * (x.2 : ℝ)⌋₊)
    (⌊(l : ℝ) * (x.1 : ℝ)⌋₊, ⌊(l : ℝ) * (x.2 : ℝ)⌋₊)
  have hm : (∫ ω : Environment, lastPassage ω 0
        ((⌊(k : ℝ) * (x.1 : ℝ)⌋₊, ⌊(k : ℝ) * (x.2 : ℝ)⌋₊) +
          (⌊(l : ℝ) * (x.1 : ℝ)⌋₊, ⌊(l : ℝ) * (x.2 : ℝ)⌋₊)) ∂environmentLaw μ) -
      ((⌊(k : ℝ) * (x.1 : ℝ)⌋₊ + ⌊(l : ℝ) * (x.1 : ℝ)⌋₊ +
          (⌊(k : ℝ) * (x.2 : ℝ)⌋₊ + ⌊(l : ℝ) * (x.2 : ℝ)⌋₊) : ℕ) : ℝ) * (∫ t : ℝ, t ∂μ) ≤
    (∫ ω : Environment, lastPassage ω 0
        (⌊((k + l : ℕ) : ℝ) * (x.1 : ℝ)⌋₊, ⌊((k + l : ℕ) : ℝ) * (x.2 : ℝ)⌋₊)
          ∂environmentLaw μ) -
      ((⌊((k + l : ℕ) : ℝ) * (x.1 : ℝ)⌋₊ + ⌊((k + l : ℕ) : ℝ) * (x.2 : ℝ)⌋₊ : ℕ) : ℝ) *
        (∫ t : ℝ, t ∂μ) :=
    integral_lastPassage_corrected_monotone μ hμ
      ((⌊(k : ℝ) * (x.1 : ℝ)⌋₊, ⌊(k : ℝ) * (x.2 : ℝ)⌋₊) +
        (⌊(l : ℝ) * (x.1 : ℝ)⌋₊, ⌊(l : ℝ) * (x.2 : ℝ)⌋₊))
      (⌊((k + l : ℕ) : ℝ) * (x.1 : ℝ)⌋₊, ⌊((k + l : ℕ) : ℝ) * (x.2 : ℝ)⌋₊) hsum1 hsum2
  have hlen : ((⌊(k : ℝ) * (x.1 : ℝ)⌋₊ + ⌊(l : ℝ) * (x.1 : ℝ)⌋₊ +
          (⌊(k : ℝ) * (x.2 : ℝ)⌋₊ + ⌊(l : ℝ) * (x.2 : ℝ)⌋₊) : ℕ) : ℝ) =
      ((⌊(k : ℝ) * (x.1 : ℝ)⌋₊ + ⌊(k : ℝ) * (x.2 : ℝ)⌋₊ : ℕ) : ℝ) +
        ((⌊(l : ℝ) * (x.1 : ℝ)⌋₊ + ⌊(l : ℝ) * (x.2 : ℝ)⌋₊ : ℕ) : ℝ) := by
    simp only [Nat.cast_add]
    ring
  rw [hlen] at hm
  linarith [hs, hm]

/-- The corrected expected floor sequence has an `EReal` limit `s` for `a n / n`,
and the expected floor rate is that limit plus the linear mean term `m (x₁ + x₂)`.
Private input to the public rate theorems. -/
private theorem floor_rate_limit
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ) (x : Quadrant) :
    ∃ s : EReal,
      Tendsto (fun n : ℕ => ((((∫ ω : Environment, lastPassage ω 0
          (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) ∂environmentLaw μ) /
          (n : ℝ)) : ℝ) : EReal))
        atTop (𝓝 (s + (((∫ t : ℝ, t ∂μ) * ((x.1 : ℝ) + (x.2 : ℝ)) : ℝ) : EReal))) ∧
      ∀ n : ℕ, 0 < n →
        (((((∫ ω : Environment, lastPassage ω 0
          (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) ∂environmentLaw μ) -
          ((⌊(n : ℝ) * (x.1 : ℝ)⌋₊ + ⌊(n : ℝ) * (x.2 : ℝ)⌋₊ : ℕ) : ℝ) * (∫ t : ℝ, t ∂μ)) /
          (n : ℝ)) : ℝ) : EReal) ≤ s := by
  obtain ⟨s, hlim, hle, -⟩ := ereal_fekete_superadditive
    (fun n : ℕ => (∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) ∂environmentLaw μ) -
      ((⌊(n : ℝ) * (x.1 : ℝ)⌋₊ + ⌊(n : ℝ) * (x.2 : ℝ)⌋₊ : ℕ) : ℝ) * (∫ t : ℝ, t ∂μ))
    (fun p q _ _ => corrected_floor_superadd_index μ hμ x p q)
  refine ⟨s, ?_, hle⟩
  have hlenlim := tendsto_floor_pair_length (x.1 : ℝ) (x.2 : ℝ)
    (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)
  have hEmlim : Tendsto (fun n : ℕ =>
      (((∫ t : ℝ, t ∂μ) * (((⌊(n : ℝ) * (x.1 : ℝ)⌋₊ + ⌊(n : ℝ) * (x.2 : ℝ)⌋₊ : ℕ) : ℝ) /
          (n : ℝ)) : ℝ) : EReal))
        atTop (𝓝 (((∫ t : ℝ, t ∂μ) * ((x.1 : ℝ) + (x.2 : ℝ)) : ℝ) : EReal)) :=
    EReal.tendsto_coe.mpr (hlenlim.const_mul (∫ t : ℝ, t ∂μ))
  have hsplit : ∀ n : ℕ,
      ((((∫ ω : Environment, lastPassage ω 0
          (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) ∂environmentLaw μ) /
          (n : ℝ)) : ℝ) : EReal) =
      (((((∫ ω : Environment, lastPassage ω 0
          (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) ∂environmentLaw μ) -
          ((⌊(n : ℝ) * (x.1 : ℝ)⌋₊ + ⌊(n : ℝ) * (x.2 : ℝ)⌋₊ : ℕ) : ℝ) * (∫ t : ℝ, t ∂μ)) /
          (n : ℝ)) : ℝ) : EReal) +
      (((∫ t : ℝ, t ∂μ) * (((⌊(n : ℝ) * (x.1 : ℝ)⌋₊ + ⌊(n : ℝ) * (x.2 : ℝ)⌋₊ : ℕ) : ℝ) /
          (n : ℝ)) : ℝ) : EReal) := by
    intro n
    rw [← EReal.coe_add]
    congr 1
    ring
  have hcont : ContinuousAt (fun p : EReal × EReal => p.1 + p.2)
      (s, (((∫ t : ℝ, t ∂μ) * ((x.1 : ℝ) + (x.2 : ℝ)) : ℝ) : EReal)) :=
    EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))
  exact Tendsto.congr (fun n => (hsplit n).symm)
    (hcont.tendsto.comp (hlim.prodMk_nhds hEmlim))

/-- Lower bound: any `EReal` limit of the expected floor rate dominates the
mean times the length of the direction. The corrected means are nonnegative,
since the corrected mean is monotone and vanishes at the origin. See Martin (2004),
definition (2.3), with monotonicity from (2.2). -/
theorem expected_floor_rate_ereal_lower_bound
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ) (x : Quadrant) (g : EReal)
    (hg : Tendsto (fun n : ℕ => ((((∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) ∂environmentLaw μ) /
        (n : ℝ)) : ℝ) : EReal)) atTop (𝓝 g)) :
    (((∫ t : ℝ, t ∂μ) * ((x.1 : ℝ) + (x.2 : ℝ)) : ℝ) : EReal) ≤ g := by
  have hlenlim := tendsto_floor_pair_length (x.1 : ℝ) (x.2 : ℝ)
    (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)
  have hmlim := EReal.tendsto_coe.mpr (hlenlim.const_mul (∫ t : ℝ, t ∂μ))
  refine le_of_tendsto_of_tendsto' hmlim hg (fun n => EReal.coe_le_coe_iff.mpr ?_)
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    simp
  · have hB := integral_lastPassage_corrected_monotone μ hμ 0
      (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) (Nat.zero_le _) (Nat.zero_le _)
    have hz0 : ∀ ω : Environment, lastPassage ω 0 (0 : ℕ × ℕ) = 0 :=
      fun ω => lastPassage_zero ω 0
    have hz : (∫ ω : Environment, lastPassage ω 0 (0 : ℕ × ℕ) ∂environmentLaw μ) = 0 := by
      simp only [hz0, integral_zero]
    have hlen0 : (((0 : ℕ × ℕ).1 + (0 : ℕ × ℕ).2 : ℕ) : ℝ) * (∫ t : ℝ, t ∂μ) = 0 := by
      simp
    have hB' : (0 : ℝ) ≤ (∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) ∂environmentLaw μ) -
        ((⌊(n : ℝ) * (x.1 : ℝ)⌋₊ + ⌊(n : ℝ) * (x.2 : ℝ)⌋₊ : ℕ) : ℝ) * (∫ t : ℝ, t ∂μ) := by
      linarith [hB, hz, hlen0]
    have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr h
    have hrew : (∫ t : ℝ, t ∂μ) * (((⌊(n : ℝ) * (x.1 : ℝ)⌋₊ + ⌊(n : ℝ) * (x.2 : ℝ)⌋₊ : ℕ) : ℝ) /
        (n : ℝ)) =
        (((⌊(n : ℝ) * (x.1 : ℝ)⌋₊ + ⌊(n : ℝ) * (x.2 : ℝ)⌋₊ : ℕ) : ℝ) * (∫ t : ℝ, t ∂μ)) /
          (n : ℝ) := by
      ring
    rw [hrew]
    exact div_le_div_of_nonneg_right (by linarith) hnpos.le

/-- Existence: the expected floor rate `E T(⌊n x⌋) / n` converges in `EReal`
to some `g x`, which is bounded below by the mean times the length of `x`.
See Martin (2004), the introduction and definition (2.3). -/
theorem expected_floor_rate_ereal_limit_exists
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ) (x : Quadrant) :
    ∃ g : EReal,
      Tendsto (fun n : ℕ => ((((∫ ω : Environment, lastPassage ω 0
          (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) ∂environmentLaw μ) /
          (n : ℝ)) : ℝ) : EReal)) atTop (𝓝 g) := by
  obtain ⟨s, hlim, -⟩ := floor_rate_limit μ hμ x
  exact ⟨_, hlim⟩

/-- The expected floor rate in `EReal` is never `-∞`: its limit is at least the
mean times the length of the direction. See Martin (2004), definition (2.3). -/
theorem expected_floor_rate_ereal_bot_lt
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ) (x : Quadrant) (g : EReal)
    (hg : Tendsto (fun n : ℕ => ((((∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) ∂environmentLaw μ) /
        (n : ℝ)) : ℝ) : EReal)) atTop (𝓝 g)) :
    (⊥ : EReal) < g :=
  lt_of_lt_of_le (EReal.bot_lt_coe _) (expected_floor_rate_ereal_lower_bound μ hμ x g hg)

/-- Per-`n` lower bound: for every `n ≥ 1`, the rate `g x` dominates the corrected
mean at `n`, divided by `n`, plus the linear term. -/
theorem expected_floor_rate_ereal_per_n_lower_bound
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ) (x : Quadrant) (g : EReal)
    (hg : Tendsto (fun n : ℕ => ((((∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) ∂environmentLaw μ) /
        (n : ℝ)) : ℝ) : EReal)) atTop (𝓝 g))
    (n : ℕ) (hn : 0 < n) :
    ((((∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) ∂environmentLaw μ) -
        ((⌊(n : ℝ) * (x.1 : ℝ)⌋₊ + ⌊(n : ℝ) * (x.2 : ℝ)⌋₊ : ℕ) : ℝ) * (∫ t : ℝ, t ∂μ)) /
        (n : ℝ) + (∫ t : ℝ, t ∂μ) * ((x.1 : ℝ) + (x.2 : ℝ)) : ℝ) : EReal) ≤ g := by
  obtain ⟨s, hlim, hle⟩ := floor_rate_limit μ hμ x
  have hgs : g = s + (((∫ t : ℝ, t ∂μ) * ((x.1 : ℝ) + (x.2 : ℝ)) : ℝ) : EReal) :=
    tendsto_nhds_unique hg hlim
  rw [hgs, EReal.coe_add]
  exact add_le_add (hle n hn) le_rfl

/-- Finite-case linear bound: if the rate is finite, the expected passage at
every `n ≥ 1` is at most `n` times the rate plus `2 |m|`, where `m` is the mean.
See Martin (2004), definition (2.3). -/
theorem expected_floor_rate_ereal_linear_bound
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ) (x : Quadrant) (g : EReal)
    (hg : Tendsto (fun n : ℕ => ((((∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) ∂environmentLaw μ) /
        (n : ℝ)) : ℝ) : EReal)) atTop (𝓝 g))
    (hgtop : g ≠ ⊤) (n : ℕ) (hn : 0 < n) :
    (∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) ∂environmentLaw μ) ≤
      (n : ℝ) * g.toReal + 2 * |(∫ t : ℝ, t ∂μ)| := by
  have hbot := expected_floor_rate_ereal_lower_bound μ hμ x g hg
  have hgbot : g ≠ ⊥ := by
    rintro rfl
    exact EReal.coe_ne_bot _ (le_bot_iff.mp hbot)
  have hgeq : ((g.toReal : ℝ) : EReal) = g := EReal.coe_toReal hgtop hgbot
  have hP := expected_floor_rate_ereal_per_n_lower_bound μ hμ x g hg n hn
  rw [← hgeq] at hP
  have hreal := EReal.coe_le_coe_iff.mp hP
  generalize g.toReal = r at hreal ⊢
  have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have h5 : ((∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) ∂environmentLaw μ) -
        ((⌊(n : ℝ) * (x.1 : ℝ)⌋₊ + ⌊(n : ℝ) * (x.2 : ℝ)⌋₊ : ℕ) : ℝ) * (∫ t : ℝ, t ∂μ)) /
        (n : ℝ) ≤ r - (∫ t : ℝ, t ∂μ) * ((x.1 : ℝ) + (x.2 : ℝ)) := by
    linarith
  have hA := (div_le_iff₀ hnpos).mp h5
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hf1 : ((⌊(n : ℝ) * (x.1 : ℝ)⌋₊ : ℕ) : ℝ) ≤ (n : ℝ) * (x.1 : ℝ) :=
    Nat.floor_le (mul_nonneg hn0 (NNReal.coe_nonneg _))
  have hf2 : (n : ℝ) * (x.1 : ℝ) < ((⌊(n : ℝ) * (x.1 : ℝ)⌋₊ : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hf3 : ((⌊(n : ℝ) * (x.2 : ℝ)⌋₊ : ℕ) : ℝ) ≤ (n : ℝ) * (x.2 : ℝ) :=
    Nat.floor_le (mul_nonneg hn0 (NNReal.coe_nonneg _))
  have hf4 : (n : ℝ) * (x.2 : ℝ) < ((⌊(n : ℝ) * (x.2 : ℝ)⌋₊ : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hL : ((⌊(n : ℝ) * (x.1 : ℝ)⌋₊ + ⌊(n : ℝ) * (x.2 : ℝ)⌋₊ : ℕ) : ℝ) =
      ((⌊(n : ℝ) * (x.1 : ℝ)⌋₊ : ℕ) : ℝ) + ((⌊(n : ℝ) * (x.2 : ℝ)⌋₊ : ℕ) : ℝ) :=
    Nat.cast_add _ _
  have ht : |((⌊(n : ℝ) * (x.1 : ℝ)⌋₊ + ⌊(n : ℝ) * (x.2 : ℝ)⌋₊ : ℕ) : ℝ) -
      (n : ℝ) * ((x.1 : ℝ) + (x.2 : ℝ))| ≤ 2 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have hmt : (∫ t : ℝ, t ∂μ) * (((⌊(n : ℝ) * (x.1 : ℝ)⌋₊ + ⌊(n : ℝ) * (x.2 : ℝ)⌋₊ : ℕ) : ℝ) -
      (n : ℝ) * ((x.1 : ℝ) + (x.2 : ℝ))) ≤ 2 * |(∫ t : ℝ, t ∂μ)| := by
    calc (∫ t : ℝ, t ∂μ) * (((⌊(n : ℝ) * (x.1 : ℝ)⌋₊ + ⌊(n : ℝ) * (x.2 : ℝ)⌋₊ : ℕ) : ℝ) -
          (n : ℝ) * ((x.1 : ℝ) + (x.2 : ℝ)))
        ≤ |(∫ t : ℝ, t ∂μ) * (((⌊(n : ℝ) * (x.1 : ℝ)⌋₊ + ⌊(n : ℝ) * (x.2 : ℝ)⌋₊ : ℕ) : ℝ) -
          (n : ℝ) * ((x.1 : ℝ) + (x.2 : ℝ)))| := le_abs_self _
      _ = |(∫ t : ℝ, t ∂μ)| * |((⌊(n : ℝ) * (x.1 : ℝ)⌋₊ + ⌊(n : ℝ) * (x.2 : ℝ)⌋₊ : ℕ) : ℝ) -
          (n : ℝ) * ((x.1 : ℝ) + (x.2 : ℝ))| := abs_mul _ _
      _ ≤ |(∫ t : ℝ, t ∂μ)| * 2 := mul_le_mul_of_nonneg_left ht (abs_nonneg _)
      _ = 2 * |(∫ t : ℝ, t ∂μ)| := by ring
  linarith [hA, hmt]

end LPPDifferentiability
