/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import LPP_Foundations.Frozen.Model.LastPassage
public import LPP_Foundations.Frozen.Model.Quadrant
public import Martin2004.Probability.BlockingComparison
public import Martin2004.Probability.GaussianBlockComparison
public import Martin2004.Probability.MartinBoundedContinuity
public import Martin2004.Probability.MeanVarianceTruncationTail
public import Martin2004.Probability.ShapeComparison
public import Martin2004.Shape.ExpectedRateShape
import Martin2004.Probability.GaussianBlockComparisonBound
import ProbabilityBasics.Probability.SqrtCdfDistance

@[expose] public section

/-!
# Universality of the boundary behaviour (Lemma 4.6 of Martin (2004))

Martin (2004), Lemma 4.6, is the following. Let `μ` satisfy the square-root tail conditions
(2.6) and (2.7), with mean `m` and variance `s²`, and let `r(α)` tend to infinity with
`r(α) √α → 0` as `α ↓ 0`. Then
`(g(1, α) - m - s gΦ(1, α r) / √r) / √α → 0` as `α ↓ 0` (formula (4.7) of Martin (2004)).

The proof follows Martin's. Given `ε`, Lemma 4.3 gives a law `ν₀` with bounded support, the same
mean and variance, and square-root distance below `ε/8`. (Martin uses `ε/2` and ends with `ε`;
the constants here are chosen differently.) The quantity for `μ` is the quantity for `ν₀` plus
`(g - h)/√α`, where `h` is the shape of `ν₀`.
* `shape_diff_le`: the second term, by Lemma 4.2 (equal means), is at most `2 √(1 + α) ε/8`.
* `universality_of_bounded`: the first term tends to `0` by Lemmas 4.4 and 4.5 applied to `ν₀`.
The shapes of `ν₀` and of the block laws are obtained from the existence theorem for bounded laws.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace LPPDifferentiability

/-! ### Second term of the split: Lemma 4.2 -/

/-- The last display of the proof of Martin (2004), Lemma 4.6: if two laws satisfy the tail
conditions and have the same
mean and have square-root distance below `ε`, then `|g(1, α) - h(1, α)| / √α ≤ 2 √(1 + α) ε`. -/
private lemma shape_diff_le (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hneg₁ : (∫⁻ t in Iio (0 : ℝ), (μ (Iic t)) ^ (1 / 2 : ℝ)) < ∞)
    (hpos₁ : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞)
    (hneg₂ : (∫⁻ t in Iio (0 : ℝ), (ν (Iic t)) ^ (1 / 2 : ℝ)) < ∞)
    (hpos₂ : (∫⁻ t in Ioi (0 : ℝ), (ν (Ioi t)) ^ (1 / 2 : ℝ)) < ∞)
    (hmean : ∫ t : ℝ, t ∂ν = ∫ t : ℝ, t ∂μ)
    (g h : Quadrant → ℝ) (hg : IsExpectedRateShape μ g) (hh : IsExpectedRateShape ν h)
    (ε : ℝ) (hε : 0 < ε)
    (hJ : sqrtCdfDistance μ ν < ENNReal.ofReal ε)
    (α : ℝ≥0) (hα : 0 < α) :
    |g (1, α) - h (1, α)| / Real.sqrt (α : ℝ) ≤ 2 * Real.sqrt (1 + (α : ℝ)) * ε := by
  have h42 := martin_lemma_4_2 μ ν hneg₁ hpos₁ hneg₂ hpos₂ g h hg hh α hα
  rw [hmean, sub_self, mul_zero, sub_zero] at h42
  change _ ≤ _ * sqrtCdfDistance μ ν at h42
  have hc : 0 ≤ 2 * Real.sqrt ((α : ℝ) * (1 + (α : ℝ))) := by positivity
  have h1 : ENNReal.ofReal |g (1, α) - h (1, α)| ≤
      ENNReal.ofReal (2 * Real.sqrt ((α : ℝ) * (1 + (α : ℝ))) * ε) := by
    refine h42.trans ?_
    rw [ENNReal.ofReal_mul hc]
    exact mul_le_mul' le_rfl hJ.le
  have hRHS : 0 ≤ 2 * Real.sqrt ((α : ℝ) * (1 + (α : ℝ))) * ε := by positivity
  have h2 := (ENNReal.ofReal_le_ofReal_iff hRHS).1 h1
  have hs : 0 < Real.sqrt (α : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hα)
  rw [div_le_iff₀ hs]
  calc |g (1, α) - h (1, α)| ≤ 2 * Real.sqrt ((α : ℝ) * (1 + (α : ℝ))) * ε := h2
    _ = 2 * Real.sqrt (1 + (α : ℝ)) * ε * Real.sqrt (α : ℝ) := by
        rw [Real.sqrt_mul (NNReal.coe_nonneg α)]
        ring

/-! ### First term of the split: Lemmas 4.4 and 4.5 -/

/--
Martin (2004), Lemmas 4.4 and 4.5 control the comparisons from the bounded law to block sums
and from those sums to the Gaussian shape. Each block law has an expected-rate shape because
it too has bounded support. Choose r(α) tending to infinity with √α r(α) tending to zero
to make both comparison errors vanish.
-/
private lemma universality_of_bounded (ν₀ : Measure ℝ) [IsProbabilityMeasure ν₀] (L : ℝ)
    (hL : ∀ᵐ t ∂ν₀, |t| ≤ L)
    (r : ℝ≥0 → ℕ) (hr1 : ∀ α, 1 ≤ r α)
    (hr : Tendsto (fun α => (r α : ℝ)) (𝓝[>] (0 : ℝ≥0)) atTop)
    (hrα : Tendsto (fun α : ℝ≥0 => (r α : ℝ) * Real.sqrt (α : ℝ)) (𝓝[>] (0 : ℝ≥0)) (𝓝 0))
    (g₀ gΦ : Quadrant → ℝ) (hg₀ : IsExpectedRateShape ν₀ g₀)
    (hΦ : ∀ x : Quadrant, Tendsto (fun n : ℕ =>
        (∫ ω : Environment, lastPassage ω 0
          (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
          ∂environmentLaw (gaussianReal 0 1)) / (n : ℝ)) atTop (𝓝 (gΦ x))) :
    Tendsto (fun α : ℝ≥0 =>
      (g₀ (1, α) - (∫ t : ℝ, t ∂ν₀) -
        Real.sqrt (∫ t : ℝ, (t - ∫ s : ℝ, s ∂ν₀) ^ 2 ∂ν₀) *
          gΦ (1, α * (r α : ℝ≥0)) / Real.sqrt (r α : ℝ)) / Real.sqrt (α : ℝ))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 0) := by
  have hL0 : 0 ≤ L := by
    obtain ⟨x, hx⟩ := hL.exists
    exact (abs_nonneg x).trans hx
  -- the laws of the sums of `k` independent copies of `ν₀`
  obtain ⟨ν, hν⟩ : ∃ ν : ℕ → Measure ℝ,
      ∀ k, ν k = (Measure.pi (fun _ : Fin k => ν₀)).map (fun y => ∑ i, y i) :=
    ⟨fun k => (Measure.pi (fun _ : Fin k => ν₀)).map (fun y => ∑ i, y i), fun k => rfl⟩
  have hνprob : ∀ k, IsProbabilityMeasure (ν k) := fun k => by
    rw [hν k]
    infer_instance
  have := hνprob
  -- their shapes: `ν k` is bounded by `k L`
  have hex : ∀ k : ℕ, ∃ G : Quadrant → ℝ, IsExpectedRateShape (ν k) G := fun k => by
    obtain ⟨G, hG, -⟩ := exists_unique_continuous_lastPassage_real_expected_rate_of_ae_abs_le
      (ν k) (k * L) (mul_nonneg (Nat.cast_nonneg k) hL0) (abs_sum_law_le ν₀ L hL k (ν k) (hν k))
    exact ⟨G, hG.1.1.1⟩
  choose G hG using hex
  -- Lemma 4.4 compares `g₀(1, α)` with `G_r(1, α r)/r`
  have h44 := martin_lemma_4_4 ν₀ ⟨L, hL⟩ r hr hrα ν hν hg₀ (fun k _ => hG k)
  -- Lemma 4.5 compares `G_r(1, α r)/r` with the Gaussian shape
  have h45 := martin_lemma_4_5 ν₀ L hL r hr1 hr hrα ν hν G (fun k => hG k) gΦ hΦ
  have hsum := h44.add h45
  rw [add_zero] at hsum
  refine hsum.congr fun α => ?_
  ring

/-! ### Splitting the quantity -/

/-- The triangle inequality for the split of the quantity: `a - c - d = (b - c - d) + (a - b)`. -/
private lemma abs_div_sub_le (a b c d s : ℝ) (hs : 0 < s) :
    |(a - c - d) / s| ≤ |(b - c - d) / s| + |a - b| / s := by
  have hsplit : (a - c - d) / s = (b - c - d) / s + (a - b) / s := by ring
  rw [hsplit, ← abs_of_pos hs, ← abs_div, abs_of_pos hs]
  exact abs_add_le _ _

/-! ### Martin, Lemma 4.6 -/

/-- **Martin (2004), Lemma 4.6**, the universality statement (4.7). For a law `μ` with
the square-root tail conditions (2.6) and (2.7), mean `m` and variance `s²`, and shape `g`, and
for `r(α)`
tending to infinity with `r(α) √α → 0` as `α ↓ 0`, with `gΦ` the shape for standard normal weights,
`(g(1, α) - m - s gΦ(1, α r) / √r) / √α → 0` as `α ↓ 0`. The proof truncates `μ` by Lemma 4.3,
compares
the shapes by Lemma 4.2, and uses Lemmas 4.4 and 4.5 for the truncated law. -/
theorem martin_lemma_4_6
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : (∫⁻ t in Iio (0 : ℝ), (μ (Iic t)) ^ (1 / 2 : ℝ)) < ∞)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞)
    (r : ℝ≥0 → ℕ) (hr1 : ∀ α, 1 ≤ r α)
    (hr : Tendsto (fun α => (r α : ℝ)) (𝓝[>] (0 : ℝ≥0)) atTop)
    (hrα : Tendsto (fun α : ℝ≥0 => (r α : ℝ) * Real.sqrt (α : ℝ)) (𝓝[>] (0 : ℝ≥0)) (𝓝 0))
    (g : Quadrant → ℝ)
    (hg : ∀ x : Quadrant, Tendsto (fun n : ℕ =>
        (∫ ω : Environment, lastPassage ω 0
          (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
          ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (g x)))
    (gΦ : Quadrant → ℝ)
    (hΦ : ∀ x : Quadrant, Tendsto (fun n : ℕ =>
        (∫ ω : Environment, lastPassage ω 0
          (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
          ∂environmentLaw (gaussianReal 0 1)) / (n : ℝ)) atTop (𝓝 (gΦ x))) :
    Tendsto (fun α : ℝ≥0 =>
      (g (1, α) - (∫ t : ℝ, t ∂μ) -
        Real.sqrt (∫ t : ℝ, (t - ∫ s : ℝ, s ∂μ) ^ 2 ∂μ) *
          gΦ (1, α * (r α : ℝ≥0)) / Real.sqrt (r α : ℝ)) / Real.sqrt (α : ℝ))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 0) := by
  -- let ε > 0; the target is `dist (quantity α) 0 < ε` eventually
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- step 1: Lemma 4.3 gives `ν₀` with bounded support, the same mean and variance,
  -- and square-root distance below `ε / 8`
  obtain ⟨ν₀, hν₀, ⟨L, hL⟩, hmean, hvar, hJ⟩ :=
    martin_truncation_mean_variance μ hneg hpos (ε / 8) (by positivity)
  have := hν₀
  have hL0 : 0 ≤ L := by
    obtain ⟨x, hx⟩ := hL.exists
    exact (abs_nonneg x).trans hx
  -- the tails of `ν₀` and its shape `h₀`
  obtain ⟨hneg₂, hpos₂⟩ := sqrt_tails_of_bounded ν₀ L hL
  obtain ⟨h₀, hh₀, -⟩ :=
    exists_unique_continuous_lastPassage_real_expected_rate_of_ae_abs_le ν₀ L hL0 hL
  have hshape : IsExpectedRateShape ν₀ h₀ := hh₀.1.1.1
  -- step 3: the first term, for `ν₀`, with the mean and variance of `μ`
  have hfirst := universality_of_bounded ν₀ L hL r hr1 hr hrα h₀ gΦ hshape hΦ
  rw [hvar, hmean, Metric.tendsto_nhds] at hfirst
  have hfirst' := hfirst (ε / 2) (by positivity)
  have hpos' : ∀ᶠ α in 𝓝[>] (0 : ℝ≥0), 0 < α := self_mem_nhdsWithin
  have hle : ∀ᶠ α in 𝓝[>] (0 : ℝ≥0), α ≤ 3 :=
    nhdsWithin_le_nhds (Iic_mem_nhds (by norm_num : (0 : ℝ≥0) < 3))
  filter_upwards [hfirst', hpos', hle] with α hα hαpos hα3
  -- step 4: the second term, by Lemma 4.2 and the distance bound
  have hdist : sqrtCdfDistance μ ν₀ < ENNReal.ofReal (ε / 8) := by
    rw [sqrtCdfDistance_eq_lintegral_ofReal_rpow]
    exact hJ
  have hd := shape_diff_le μ ν₀ hneg hpos hneg₂ hpos₂ hmean g h₀ hg hshape (ε / 8)
    (by positivity) hdist α hαpos
  have hs : 0 < Real.sqrt (α : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hαpos)
  have hsq : Real.sqrt (1 + (α : ℝ)) ≤ 2 := by
    refine Real.sqrt_le_iff.2 ⟨by norm_num, ?_⟩
    have : (α : ℝ) ≤ 3 := by exact_mod_cast hα3
    linarith
  have hd' : 2 * Real.sqrt (1 + (α : ℝ)) * (ε / 8) ≤ ε / 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hsq) hε.le]
  -- step 2: the triangle inequality
  rw [Real.dist_eq, sub_zero] at hα ⊢
  exact lt_of_le_of_lt (abs_div_sub_le _ (h₀ (1, α)) _ _ _ hs)
    (by linarith)

end LPPDifferentiability
