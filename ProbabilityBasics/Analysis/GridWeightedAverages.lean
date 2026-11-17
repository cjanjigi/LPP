/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-! Fixed-grid approximation for affine weights on finite prefix sums. -/

public section
open Filter
open scoped BigOperators Topology

namespace ProbabilityBasics

private theorem sum_consecutive_grid (p : ℕ → ℕ) (hp : Monotone p)
    (hzero : p 0 = 0) (m : ℕ) (f : ℕ → ℝ) :
    (∑ k ∈ Finset.range (p m), f k) =
      ∑ q ∈ Finset.range m, ∑ k ∈ Finset.Ico (p q) (p (q + 1)), f k := by
  induction m with
  | zero => simp [hzero]
  | succ m ih =>
    rw [Finset.sum_range_succ, ← ih]
    exact (Finset.sum_range_add_sum_Ico f (hp (Nat.le_succ m))).symm

/-- Fixed-grid prefix convergence and a uniform absolute-sum bound imply
convergence for every affine weight. This is the deterministic step-approximation
used in JR arXiv:1810.03580v3, Appendix B, Lemma B.5. -/
theorem tendsto_affine_weighted_prefix_sums_of_grid_limits
    (a : ℕ → ℕ → ℝ) (b : ℝ) (hb : 0 < b) (r : ℕ)
    (hprefix : ∀ m : ℕ, 0 < m → ∀ q : ℕ, q ≤ m →
      Tendsto (fun n : ℕ =>
        (∑ k ∈ Finset.range ⌊(n : ℝ) * b * (q : ℝ) / (m : ℝ)⌋₊,
          a n k) / (n : ℝ)^r) atTop (𝓝 0))
    (habs : BddAbove (Set.range (fun n : ℕ =>
      (∑ k ∈ Finset.range ⌊(n : ℝ) * b⌋₊, |a n k|) / (n : ℝ)^r))) :
    ∀ c d : ℝ, Tendsto (fun n : ℕ =>
      (∑ k ∈ Finset.range ⌊(n : ℝ) * b⌋₊,
        (c + d * (((k : ℝ) + 1) / (n : ℝ))) * a n k) / (n : ℝ)^r)
      atTop (𝓝 0) := by
  classical
  intro c d
  obtain ⟨C₀, hC₀⟩ := habs
  let C : ℝ := max C₀ 1
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hC (n : ℕ) :
      (∑ k ∈ Finset.range ⌊(n : ℝ) * b⌋₊, |a n k|) / (n : ℝ)^r ≤ C :=
    (hC₀ ⟨n, rfl⟩).trans (le_max_left _ _)
  let p : ℕ → ℕ → ℕ → ℕ := fun m n q =>
    ⌊(n : ℝ) * b * (q : ℝ) / (m : ℝ)⌋₊
  have hp (m n : ℕ) : Monotone (p m n) := by
    intro q q' hq
    apply Nat.floor_mono
    gcongr
  have hp0 (m n : ℕ) : p m n 0 = 0 := by simp [p]
  have hpm (m n : ℕ) (hm : 0 < m) : p m n m = ⌊(n : ℝ) * b⌋₊ := by
    have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
    simp [p, hm']
  let w : ℕ → ℕ → ℝ := fun m q => c + d * (b * (q : ℝ) / (m : ℝ))
  let step : ℕ → ℕ → ℝ := fun m n =>
    (∑ q ∈ Finset.range m, ∑ k ∈ Finset.Ico (p m n q) (p m n (q + 1)),
      w m q * a n k) / (n : ℝ)^r
  let target : ℕ → ℝ := fun n =>
    (∑ k ∈ Finset.range ⌊(n : ℝ) * b⌋₊,
      (c + d * (((k : ℝ) + 1) / (n : ℝ))) * a n k) / (n : ℝ)^r
  change Tendsto target atTop (𝓝 0)
  have hstep (m : ℕ) (hm : 0 < m) : Tendsto (step m) atTop (𝓝 0) := by
    have hterm (q : ℕ) (hq : q ∈ Finset.range m) :
        Tendsto (fun n : ℕ => w m q *
          (((∑ k ∈ Finset.range (p m n (q + 1)), a n k) / (n : ℝ)^r) -
           ((∑ k ∈ Finset.range (p m n q), a n k) / (n : ℝ)^r))) atTop (𝓝 0) := by
      have hq' : q < m := Finset.mem_range.mp hq
      have hnext := hprefix m hm (q + 1) (Nat.succ_le_of_lt hq')
      have hprev := hprefix m hm q (Nat.le_of_lt hq')
      simpa only [sub_zero, mul_zero, p] using (hnext.sub hprev).const_mul (w m q)
    have hsum := tendsto_finsetSum (Finset.range m) hterm
    have hsame (n : ℕ) : step m n = ∑ q ∈ Finset.range m, w m q *
          (((∑ k ∈ Finset.range (p m n (q + 1)), a n k) / (n : ℝ)^r) -
           ((∑ k ∈ Finset.range (p m n q), a n k) / (n : ℝ)^r)) := by
      dsimp [step]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro q hq
      rw [← Finset.mul_sum, Finset.sum_Ico_eq_sub _ (hp m n (Nat.le_succ q))]
      ring
    simpa only [Finset.sum_const_zero] using hsum.congr' (Eventually.of_forall fun n => (hsame n).symm)
  have hcell (m n q k : ℕ) (hm : 0 < m) (hn : 0 < n)
      (hk : k ∈ Finset.Ico (p m n q) (p m n (q + 1))) :
      |((k : ℝ) + 1) / (n : ℝ) - b * (q : ℝ) / (m : ℝ)| ≤ b / (m : ℝ) := by
    have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
    have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    have hleft := Nat.lt_floor_add_one ((n : ℝ) * b * (q : ℝ) / (m : ℝ))
    have hright := Nat.floor_le (show 0 ≤ (n : ℝ) * b * ((q + 1 : ℕ) : ℝ) / (m : ℝ) by positivity)
    have hkl : p m n q ≤ k := (Finset.mem_Ico.mp hk).1
    have hkr : k < p m n (q + 1) := (Finset.mem_Ico.mp hk).2
    have hklR : (p m n q : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hkl
    have hkrR : (k : ℝ) + 1 ≤ (p m n (q + 1) : ℝ) := by exact_mod_cast hkr
    dsimp only [p] at hklR hkrR
    have hklM := mul_le_mul_of_nonneg_left hklR hmR.le
    have hkrM := mul_le_mul_of_nonneg_left hkrR hmR.le
    push_cast at hright
    push_cast at hkrM
    have hLower : b * (q : ℝ) / (m : ℝ) ≤ ((k : ℝ) + 1) / (n : ℝ) := by
      apply (div_le_div_iff₀ hmR hnR).2
      have hh := (div_lt_iff₀ hmR).mp hleft
      nlinarith only [hh, hklM]
    have hUpper : ((k : ℝ) + 1) / (n : ℝ) ≤
        b * ((q : ℝ) + 1) / (m : ℝ) := by
      apply (div_le_div_iff₀ hnR hmR).2
      have hh := (le_div_iff₀ hmR).mp hright
      nlinarith only [hh, hkrM]
    have hadd : b * ((q : ℝ) + 1) / (m : ℝ) =
        b * (q : ℝ) / (m : ℝ) + b / (m : ℝ) := by ring
    rw [hadd] at hUpper
    rw [abs_le]
    constructor <;> linarith only [hLower, hUpper]
  have herror (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
      |target n - step m n| ≤ (|d| * (b / (m : ℝ))) * C := by
    have hnorm : 0 ≤ (n : ℝ)^r := pow_nonneg (Nat.cast_nonneg n) _
    have hweight (q k : ℕ) (hk : k ∈ Finset.Ico (p m n q) (p m n (q + 1))) :
        |((c + d * (((k : ℝ) + 1) / (n : ℝ))) - w m q) * a n k| ≤
          (|d| * (b / (m : ℝ))) * |a n k| := by
      have hh := hcell m n q k hm hn hk
      have heq : (c + d * (((k : ℝ) + 1) / (n : ℝ))) - w m q =
          d * (((k : ℝ) + 1) / (n : ℝ) - b * (q : ℝ) / (m : ℝ)) := by
        dsimp [w]
        ring
      rw [heq, abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh (abs_nonneg d)) (abs_nonneg _)
    have hsum : |(∑ k ∈ Finset.range ⌊(n : ℝ) * b⌋₊,
        (c + d * (((k : ℝ) + 1) / (n : ℝ))) * a n k) -
        ∑ q ∈ Finset.range m, ∑ k ∈ Finset.Ico (p m n q) (p m n (q + 1)),
          w m q * a n k| ≤
        (|d| * (b / (m : ℝ))) * ∑ k ∈ Finset.range ⌊(n : ℝ) * b⌋₊, |a n k| := by
      rw [← hpm m n hm, sum_consecutive_grid (p m n) (hp m n) (hp0 m n)]
      rw [← Finset.sum_sub_distrib]
      calc
        _ ≤ ∑ q ∈ Finset.range m, |(∑ k ∈ Finset.Ico (p m n q) (p m n (q + 1)),
            (c + d * (((k : ℝ) + 1) / (n : ℝ))) * a n k) -
            ∑ k ∈ Finset.Ico (p m n q) (p m n (q + 1)), w m q * a n k| :=
              Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ q ∈ Finset.range m, ∑ k ∈ Finset.Ico (p m n q) (p m n (q + 1)),
              (|d| * (b / (m : ℝ))) * |a n k| := by
              apply Finset.sum_le_sum
              intro q hq
              rw [← Finset.sum_sub_distrib]
              calc
                _ ≤ ∑ k ∈ Finset.Ico (p m n q) (p m n (q + 1)),
                    |(c + d * (((k : ℝ) + 1) / (n : ℝ))) * a n k - w m q * a n k| :=
                      Finset.abs_sum_le_sum_abs _ _
                _ = ∑ k ∈ Finset.Ico (p m n q) (p m n (q + 1)),
                    |((c + d * (((k : ℝ) + 1) / (n : ℝ))) - w m q) * a n k| := by
                      apply Finset.sum_congr rfl
                      intro k hk
                      congr 1
                      ring
                _ ≤ _ := Finset.sum_le_sum (fun k hk => hweight q k hk)
        _ = _ := by
          rw [sum_consecutive_grid (p m n) (hp m n) (hp0 m n)]
          simp only [Finset.mul_sum]
    calc
      |target n - step m n| =
          |(∑ k ∈ Finset.range ⌊(n : ℝ) * b⌋₊,
            (c + d * (((k : ℝ) + 1) / (n : ℝ))) * a n k) -
            ∑ q ∈ Finset.range m, ∑ k ∈ Finset.Ico (p m n q) (p m n (q + 1)),
              w m q * a n k| / (n : ℝ)^r := by
              dsimp [target, step]
              rw [← sub_div, abs_div, abs_of_nonneg hnorm]
      _ ≤ ((|d| * (b / (m : ℝ))) * ∑ k ∈ Finset.range ⌊(n : ℝ) * b⌋₊, |a n k|) /
          (n : ℝ)^r := div_le_div_of_nonneg_right hsum hnorm
      _ = (|d| * (b / (m : ℝ))) *
          ((∑ k ∈ Finset.range ⌊(n : ℝ) * b⌋₊, |a n k|) / (n : ℝ)^r) := by ring
      _ ≤ (|d| * (b / (m : ℝ))) * C :=
        mul_le_mul_of_nonneg_left (hC n) (by positivity)
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hsmall : Tendsto (fun m : ℕ => (|d| * b * C) / (m : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  obtain ⟨m, hm, hmSmall⟩ := ((eventually_gt_atTop (0 : ℕ)).and
    (hsmall.eventually (gt_mem_nhds (half_pos hε)))).exists
  have hmBound : (|d| * (b / (m : ℝ))) * C < ε / 2 := by
    convert hmSmall using 1; ring
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hstep m hm) (ε / 2) (half_pos hε)
  refine ⟨max N 1, ?_⟩
  intro n hn
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one ((le_max_right _ _).trans hn)
  have hstepSmall : |step m n| < ε / 2 := by
    simpa only [Real.dist_eq, sub_zero] using hN n hnN
  have hh := herror m n hm hnpos
  have ht := abs_sub_le (target n) (step m n) 0
  simp only [sub_zero] at ht
  simpa only [Real.dist_eq, sub_zero] using (show |target n| < ε by linarith)

end ProbabilityBasics
