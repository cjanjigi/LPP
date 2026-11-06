/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Probability.IdentDistrib
import ProbabilityBasics.Probability.LiggettExpectedRate
import ProbabilityBasics.Probability.IdentDistribSublinear

/-!
# Sublinear Liggett remainders

The fixed-length translated intervals in Liggett's proof have the law of the
corresponding origin interval. Their integrable common law makes them
sublinear almost surely, without an independence assumption.
-/

public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace LPPDifferentiability

/-- For fixed positive interval length `j`, the translated remainders
`A (q * k) (q * k + j)` divided by the block index tend to zero almost surely.
The adjacent whole-column laws and the integrable origin interval supply the
identically distributed sequence required by the generic sublinearity lemma. -/
theorem ae_tendsto_liggett_remainder_div_block_index
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (A : ℕ → ℕ → Ω → ℝ)
    (hmeas : ∀ n : ℕ, 0 < n → Measurable (A 0 n))
    (hint : ∀ n : ℕ, 0 < n → Integrable (A 0 n) μ)
    (hadj : ∀ m : ℕ,
      IdentDistrib (fun ω (k : ℕ) => A (m + 1) (m + 1 + (k + 1)) ω)
        (fun ω (k : ℕ) => A m (m + (k + 1)) ω) μ μ)
    (k j : ℕ) (hj : 0 < j) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun q : ℕ => A (q * k) (q * k + j) ω / (q : ℝ)) atTop (𝓝 0) := by
  exact ae_tendsto_identDistrib_div_nat (hint j hj) (fun q =>
    liggett_block_identDistrib A hmeas hadj (q * k) j hj)

/-- For a positive block length, the same remainder is sublinear when divided
by its full interval length. -/
theorem ae_tendsto_liggett_remainder_div_interval_length
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (A : ℕ → ℕ → Ω → ℝ)
    (hmeas : ∀ n : ℕ, 0 < n → Measurable (A 0 n))
    (hint : ∀ n : ℕ, 0 < n → Integrable (A 0 n) μ)
    (hadj : ∀ m : ℕ,
      IdentDistrib (fun ω (k : ℕ) => A (m + 1) (m + 1 + (k + 1)) ω)
        (fun ω (k : ℕ) => A m (m + (k + 1)) ω) μ μ)
    (k j : ℕ) (hk : 0 < k) (hj : 0 < j) :
    ∀ᵐ ω ∂μ,
      Tendsto
        (fun q : ℕ => A (q * k) (q * k + j) ω / ((q * k + j : ℕ) : ℝ))
        atTop (𝓝 0) := by
  filter_upwards
    [ae_tendsto_liggett_remainder_div_block_index A hmeas hint hadj k j hj]
    with ω hω
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards
    [(Metric.tendsto_nhds.mp hω ε hε), eventually_gt_atTop (0 : ℕ)]
    with q hq hqpos
  have hqreal : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hqpos
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hk)
  have hqk : q ≤ q * k := by
    calc
      q = q * 1 := by simp only [Nat.mul_one]
      _ ≤ q * k := Nat.mul_le_mul_left q hk1
  have hdenNat : q ≤ q * k + j := hqk.trans (Nat.le_add_right _ _)
  have hden : (q : ℝ) ≤ ((q * k + j : ℕ) : ℝ) := Nat.cast_le.mpr hdenNat
  have hnorm :
      ‖A (q * k) (q * k + j) ω / ((q * k + j : ℕ) : ℝ)‖ ≤
        ‖A (q * k) (q * k + j) ω / (q : ℝ)‖ := by
    rw [norm_div, norm_div, Real.norm_natCast, Real.norm_natCast]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hqreal hden
  calc
    dist (A (q * k) (q * k + j) ω / ((q * k + j : ℕ) : ℝ)) 0 =
        ‖A (q * k) (q * k + j) ω / ((q * k + j : ℕ) : ℝ)‖ := by
          rw [dist_zero_right]
    _ ≤ ‖A (q * k) (q * k + j) ω / (q : ℝ)‖ := hnorm
    _ = dist (A (q * k) (q * k + j) ω / (q : ℝ)) 0 := by
          rw [dist_zero_right]
    _ < ε := hq

end LPPDifferentiability
