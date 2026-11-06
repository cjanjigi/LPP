/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Analysis.FiniteResidueLimits
public import Mathlib.Probability.IdentDistrib
import ProbabilityBasics.Probability.LiggettBlockDecomposition
import ProbabilityBasics.Probability.LiggettRemainders
import ProbabilityBasics.Probability.LiggettBlockAverages
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The upper bound from Liggett's block argument

The interpolation argument in Liggett (1985), equations (2.5)--(2.8). Residue zero never
uses a diagonal array entry.
-/

public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace LPPDifferentiability

private theorem limsup_liggett_le_of_block_limits
    {Ω : Type*} (A : ℕ → ℕ → Ω → ℝ) (ω : Ω)
    (k : ℕ) (hk : 0 < k) (U : ℝ)
    (hwhole : ∀ q : ℕ, 0 < q → A 0 (q * k) ω ≤
      ∑ i ∈ Finset.range q, A (i * k) ((i + 1) * k) ω)
    (hbound : ∀ j q : ℕ, 0 < j → 0 < q → A 0 (q * k + j) ω ≤
      (∑ i ∈ Finset.range q, A (i * k) ((i + 1) * k) ω) +
        A (q * k) (q * k + j) ω)
    (havg : Tendsto (fun q : ℕ =>
      (∑ i ∈ Finset.range q, A (i * k) ((i + 1) * k) ω) / (q : ℝ))
      atTop (𝓝 U))
    (hrem : ∀ j : ℕ, 0 < j → Tendsto
      (fun q : ℕ => A (q * k) (q * k + j) ω / ((q * k + j : ℕ) : ℝ))
      atTop (𝓝 0)) :
    limsup (fun n : ℕ => ((A 0 n ω / (n : ℝ) : ℝ) : EReal)) atTop ≤
      ((U / (k : ℝ) : ℝ) : EReal) := by
  apply limsup_coe_le_of_residue_eventually_lt hk
  intro c hc j _hj
  have hsum := tendsto_div_mul_add_of_tendsto_div_nat havg hk j
  by_cases hj0 : j = 0
  · subst j
    filter_upwards [hsum.eventually_lt_const hc, eventually_gt_atTop (0 : ℕ)]
      with q hq hqpos
    have hden : (0 : ℝ) ≤ ((q * k : ℕ) : ℝ) := Nat.cast_nonneg _
    calc
      A 0 (q * k + 0) ω / ((q * k + 0 : ℕ) : ℝ) =
          A 0 (q * k) ω / ((q * k : ℕ) : ℝ) := by rw [Nat.add_zero]
      _ ≤ (∑ i ∈ Finset.range q, A (i * k) ((i + 1) * k) ω) /
          ((q * k : ℕ) : ℝ) := div_le_div_of_nonneg_right (hwhole q hqpos) hden
      _ < c := by simpa only [Nat.add_zero] using hq
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
    have hmajor : Tendsto (fun q : ℕ =>
        (∑ i ∈ Finset.range q, A (i * k) ((i + 1) * k) ω) /
          ((q * k + j : ℕ) : ℝ) +
        A (q * k) (q * k + j) ω / ((q * k + j : ℕ) : ℝ))
        atTop (𝓝 (U / (k : ℝ))) := by
      simpa only [add_zero] using hsum.add (hrem j hjpos)
    filter_upwards [hmajor.eventually_lt_const hc, eventually_gt_atTop (0 : ℕ)]
      with q hq hqpos
    calc
      A 0 (q * k + j) ω / ((q * k + j : ℕ) : ℝ) ≤
          ((∑ i ∈ Finset.range q, A (i * k) ((i + 1) * k) ω) +
            A (q * k) (q * k + j) ω) / ((q * k + j : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right (hbound j q hjpos hqpos) (Nat.cast_nonneg _)
      _ = _ := add_div _ _ _
      _ < c := hq

/-- Block-average convergence gives Liggett's almost sure upper bound
for the extended-real limsup, using origin subadditivity and the translated
remainder laws. The supplied average may be random or deterministic. -/
theorem ae_liggett_limsup_le_of_block_average
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (A : ℕ → ℕ → Ω → ℝ)
    (hmeas : ∀ n : ℕ, 0 < n → Measurable (A 0 n))
    (hint : ∀ n : ℕ, 0 < n → Integrable (A 0 n) μ)
    (hsub : ∀ m n : ℕ, 0 < m → m < n →
      ∀ᵐ ω ∂μ, A 0 n ω ≤ A 0 m ω + A m n ω)
    (hadj : ∀ m : ℕ,
      IdentDistrib (fun ω (j : ℕ) => A (m + 1) (m + 1 + (j + 1)) ω)
        (fun ω (j : ℕ) => A m (m + (j + 1)) ω) μ μ)
    (k : ℕ) (hk : 0 < k) (U : Ω → ℝ)
    (havg : ∀ᵐ ω ∂μ, Tendsto (fun q : ℕ =>
      (∑ i ∈ Finset.range q, A (i * k) ((i + 1) * k) ω) / (q : ℝ))
      atTop (𝓝 (U ω))) :
    ∀ᵐ ω ∂μ,
      limsup (fun n : ℕ => ((A 0 (n + 1) ω / ((n + 1 : ℕ) : ℝ) : ℝ) : EReal))
        atTop ≤
        ((U ω / (k : ℝ) : ℝ) : EReal) := by
  have hwhole : ∀ᵐ ω ∂μ, ∀ q : ℕ, 0 < q → A 0 (q * k) ω ≤
      ∑ i ∈ Finset.range q, A (i * k) ((i + 1) * k) ω := by
    apply ae_all_iff.mpr
    intro q
    apply ae_all_iff.mpr
    intro hq
    exact liggett_origin_block_bound_ae A hsub k q hk hq
  have hbound : ∀ᵐ ω ∂μ, ∀ j q : ℕ, 0 < j → 0 < q →
      A 0 (q * k + j) ω ≤
        (∑ i ∈ Finset.range q, A (i * k) ((i + 1) * k) ω) +
          A (q * k) (q * k + j) ω := by
    apply ae_all_iff.mpr
    intro j
    apply ae_all_iff.mpr
    intro q
    apply ae_all_iff.mpr
    intro hj
    apply ae_all_iff.mpr
    intro hq
    exact liggett_origin_block_remainder_ae A hsub k q j hk hq hj
  have hrem : ∀ᵐ ω ∂μ, ∀ j : ℕ, 0 < j → Tendsto
      (fun q : ℕ => A (q * k) (q * k + j) ω / ((q * k + j : ℕ) : ℝ))
      atTop (𝓝 0) := by
    apply ae_all_iff.mpr
    intro j
    apply ae_all_iff.mpr
    intro hj
    exact ae_tendsto_liggett_remainder_div_interval_length A hmeas hint hadj k j hk hj
  filter_upwards [havg, hwhole, hbound, hrem] with ω hω hw hb hr
  have hlim := limsup_liggett_le_of_block_limits A ω k hk (U ω) hw hb hω hr
  exact ((tendsto_add_atTop_nat 1).limsup_comp_le_limsup
    (u := fun n : ℕ => ((A 0 n ω / (n : ℝ) : ℝ) : EReal))).trans hlim

/-- The fixed-block upper estimate in Liggett's proof of (2.2). The same
original-space witness is integrable, has the block mean divided by its length,
and bounds the extended-real upper limit of the normalized array. -/
theorem exists_liggett_limsup_upper
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (A : ℕ → ℕ → Ω → ℝ)
    (hmeas : ∀ n : ℕ, 0 < n → Measurable (A 0 n))
    (hint : ∀ n : ℕ, 0 < n → Integrable (A 0 n) μ)
    (hsub : ∀ m n : ℕ, 0 < m → m < n →
      ∀ᵐ ω ∂μ, A 0 n ω ≤ A 0 m ω + A m n ω)
    (hadj : ∀ m : ℕ,
      IdentDistrib (fun ω (j : ℕ) => A (m + 1) (m + 1 + (j + 1)) ω)
        (fun ω (j : ℕ) => A m (m + (j + 1)) ω) μ μ)
    (k : ℕ) (hk : 0 < k)
    (hstat : IdentDistrib
      (fun ω (j : ℕ) => A ((j + 2) * k) ((j + 3) * k) ω)
      (fun ω (j : ℕ) => A ((j + 1) * k) ((j + 2) * k) ω) μ μ) :
    ∃ V : Ω → ℝ, Integrable V μ ∧
      (∫ ω, V ω ∂μ) = (∫ ω, A 0 k ω ∂μ) / (k : ℝ) ∧
      ∀ᵐ ω ∂μ,
        limsup (fun n : ℕ => ((A 0 (n + 1) ω / ((n + 1 : ℕ) : ℝ) : ℝ) : EReal))
          atTop ≤ (V ω : EReal) := by
  obtain ⟨U, hU, _, havg, hmean, _⟩ :=
    exists_liggett_block_average (μ := μ) A hmeas hint hadj k hk hstat
  refine ⟨fun ω => U ω / (k : ℝ), hU.div_const _, ?_, ?_⟩
  · rw [integral_div, hmean]
  · exact ae_liggett_limsup_le_of_block_average A hmeas hint hsub hadj k hk U havg

end LPPDifferentiability
