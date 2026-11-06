/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.BoundaryUniversality
public import Martin2004.Probability.MartinRealExpectedRate
public import Martin2004.Probability.NormalExponentialTails
public import Martin2004.Shape.ExponentialShape

@[expose] public section

/-!
# Boundary asymptotics of the shape (Martin 2004, proof of Theorem 2.4)

This file follows Martin (2004), proof of Theorem 2.4. Under the square-root tails (2.6) and (2.7),
the expected-rate shape `g` of a law with mean `m` and standard deviation `s` satisfies
`g(1, α) = m + 2 s √α + o(√α)` as `α ↓ 0`.

As in Martin's proof: choose a block size `r(α)` with `r → ∞` and `r √α → 0`; apply Lemma 4.6 to
the law itself (formula (4.7)) and to the exponential law of mean 1, whose shape is `(1 + √α)²`
(formula (4.9)); eliminate the Gaussian term `gΦ(1, α r) / √r` between the two.

## Main results

- `martin_shape_boundary_asymptotics`: the expansion of `g(1, α)` at the boundary.

## References

- J. B. Martin, *Limiting shape for directed percolation models*, Ann. Probab. 32 (2004),
  Theorem 2.4 and Lemma 4.6.
-/

open MeasureTheory ProbabilityTheory Filter Set Asymptotics
open scoped NNReal ENNReal Topology

namespace LPPDifferentiability

/-- The block size used in the proof of Theorem 2.4. Martin takes `⌊α^(-1/4)⌋`; here
`r α = ⌈(√√α)⁻¹⌉ + 1`, which is at least `1` for every `α` (the statement of Lemma 4.6 asks for
`1 ≤ r α`), tends to infinity, and satisfies `r(α) √α → 0` as `α ↓ 0`. -/
private theorem exists_block_size :
    ∃ r : ℝ≥0 → ℕ, (∀ α, 1 ≤ r α) ∧
      Tendsto (fun α => (r α : ℝ)) (𝓝[>] (0 : ℝ≥0)) atTop ∧
      Tendsto (fun α : ℝ≥0 => (r α : ℝ) * Real.sqrt (α : ℝ)) (𝓝[>] (0 : ℝ≥0)) (𝓝 0) := by
  let u : ℝ≥0 → ℝ := fun α => Real.sqrt (Real.sqrt (α : ℝ))
  have hu0 : Tendsto u (𝓝[>] (0 : ℝ≥0)) (𝓝 0) := by
    have hc : Continuous u := by fun_prop
    simpa [u] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hupos : ∀ᶠ α : ℝ≥0 in 𝓝[>] (0 : ℝ≥0), 0 < u α := by
    filter_upwards [self_mem_nhdsWithin] with α hα
    exact Real.sqrt_pos.2 (Real.sqrt_pos.2 (NNReal.coe_pos.2 hα))
  have huinv : Tendsto (fun α => (u α)⁻¹) (𝓝[>] (0 : ℝ≥0)) atTop :=
    tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.2 ⟨hu0, hupos⟩)
  refine ⟨fun α => ⌈(u α)⁻¹⌉₊ + 1, fun α => Nat.le_add_left 1 _, ?_, ?_⟩
  · refine tendsto_atTop_mono (fun α => ?_) huinv
    push_cast
    linarith [Nat.le_ceil ((u α)⁻¹)]
  · have hbound : ∀ᶠ α : ℝ≥0 in 𝓝[>] (0 : ℝ≥0),
        (((⌈(u α)⁻¹⌉₊ + 1 : ℕ) : ℝ)) * Real.sqrt (α : ℝ) ≤ u α + 2 * (u α) ^ 2 := by
      filter_upwards [hupos] with α hα
      have hsq : Real.sqrt (α : ℝ) = (u α) ^ 2 := by
        simp only [u]
        rw [Real.sq_sqrt (Real.sqrt_nonneg _)]
      have hc : ((⌈(u α)⁻¹⌉₊ : ℕ) : ℝ) < (u α)⁻¹ + 1 := Nat.ceil_lt_add_one (inv_nonneg.2 hα.le)
      rw [hsq]
      push_cast
      have h2 : ((⌈(u α)⁻¹⌉₊ : ℝ) + 1) * u α ^ 2 ≤ ((u α)⁻¹ + 2) * u α ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
      have h3 : ((u α)⁻¹ + 2) * u α ^ 2 = u α + 2 * u α ^ 2 := by
        field_simp
      linarith
    have hlim : Tendsto (fun α => u α + 2 * (u α) ^ 2) (𝓝[>] (0 : ℝ≥0)) (𝓝 0) := by
      simpa using hu0.add ((hu0.pow 2).const_mul 2)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun α => by positivity) hbound

/-- The step "combining (4.7) and (4.9)" in Martin's proof of Theorem 2.4, as a statement about
real numbers. Let `q α / R α` stand for the Gaussian term `gΦ(1, α r) / √r`. If
`(gm - m - s q / R) / √α → 0` (formula (4.7) for the law) and
`((1 + 2 √α + α) - 1 - q / R) / √α → 0` (formula (4.7) for the exponential law, after inserting
the exact shape), then `(gm - (m + 2 s √α)) / √α → 0`. The quotient equals `A - s (B - √α)`,
where `A` and `B` are the two given quotients. -/
private theorem ratio_combine (gm q R : ℝ≥0 → ℝ) (m s : ℝ)
    (hA : Tendsto (fun α : ℝ≥0 => (gm α - m - s * q α / R α) / Real.sqrt (α : ℝ))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 0))
    (hB : Tendsto (fun α : ℝ≥0 =>
      ((1 + 2 * Real.sqrt (α : ℝ) + (α : ℝ)) - 1 - 1 * q α / R α) / Real.sqrt (α : ℝ))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 0)) :
    Tendsto (fun α : ℝ≥0 => (gm α - (m + 2 * s * Real.sqrt (α : ℝ))) / Real.sqrt (α : ℝ))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 0) := by
  have hsqrt : Tendsto (fun α : ℝ≥0 => Real.sqrt (α : ℝ)) (𝓝[>] (0 : ℝ≥0)) (𝓝 0) := by
    have hc : Continuous (fun α : ℝ≥0 => Real.sqrt (α : ℝ)) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hcomb := hA.sub ((hB.sub hsqrt).const_mul s)
  have hlim0 : (0 : ℝ) - s * (0 - 0) = 0 := by ring
  rw [hlim0] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with α hα
  have hs : Real.sqrt (α : ℝ) ≠ 0 := (Real.sqrt_pos.2 (NNReal.coe_pos.2 hα)).ne'
  have hsq : Real.sqrt (α : ℝ) ^ 2 = (α : ℝ) := Real.sq_sqrt (NNReal.coe_nonneg α)
  field_simp
  linear_combination s * hsq

/-- **Martin (2004), proof of Theorem 2.4.** Let `μ` satisfy the square-root tail conditions (2.6)
and (2.7) and let `g` be its expected-rate shape. Then `g(1, α) - (m + 2 s √α) = o(√α)` as
`α ↓ 0`, where `m` is the mean and `s²` the variance of `μ`. The proof compares Lemma 4.6 for `μ`
with Lemma 4.6 for the exponential law of mean 1. -/
theorem martin_shape_boundary_asymptotics
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : (∫⁻ t in Iio (0 : ℝ), (μ (Iic t)) ^ (1 / 2 : ℝ)) < ∞)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞)
    (g : Quadrant → ℝ) (hg : IsExpectedRateShape μ g) :
    (fun α : ℝ≥0 => g (1, α) - ((∫ t : ℝ, t ∂μ) +
        2 * Real.sqrt (∫ t : ℝ, (t - ∫ s : ℝ, s ∂μ) ^ 2 ∂μ) * Real.sqrt (α : ℝ)))
      =o[𝓝[>] (0 : ℝ≥0)] (fun α : ℝ≥0 => Real.sqrt (α : ℝ)) := by
  -- a block size as in Lemma 4.4
  obtain ⟨r, hr1, hr, hrα⟩ := exists_block_size
  -- the shape `gΦ` for standard normal weights, from the existence theorem under the tails
  obtain ⟨gΦ, ⟨hΦ, -⟩, -⟩ := exists_unique_lastPassage_real_expected_rate_of_martin_tails
    (gaussianReal 0 1) gaussianReal_sqrt_tails.1 gaussianReal_sqrt_tails.2
  -- formula (4.7) for `μ`
  have hA := martin_lemma_4_6 μ hneg hpos r hr1 hr hrα g hg gΦ hΦ
  -- formula (4.7) for the exponential law of mean 1 and variance 1, with its exact shape
  have hE := martin_lemma_4_6 (expMeasure 1) expMeasure_one_sqrt_tails.1
    expMeasure_one_sqrt_tails.2 r hr1 hr hrα exponentialShape isExpectedRateShape_expMeasure_one
    gΦ hΦ
  obtain ⟨hmean, hvar⟩ := expMeasure_one_mean_variance
  rw [hvar, hmean, Real.sqrt_one] at hE
  simp only [exponentialShape_one_left] at hE
  -- formula (4.9) and the combination of (4.7) and (4.9)
  have hratio := ratio_combine (fun α => g (1, α))
    (fun α => gΦ (1, α * (r α : ℝ≥0))) (fun α => Real.sqrt (r α : ℝ))
    (∫ t : ℝ, t ∂μ) (Real.sqrt (∫ t : ℝ, (t - ∫ s : ℝ, s ∂μ) ^ 2 ∂μ)) hA hE
  -- the ratio tends to `0`, which is the little-o statement since `√α ≠ 0` for `α > 0`
  refine (isLittleO_iff_tendsto' ?_).2 hratio
  filter_upwards [self_mem_nhdsWithin] with α hα h0
  exact absurd h0 (Real.sqrt_pos.2 (NNReal.coe_pos.2 hα)).ne'

end LPPDifferentiability

end
