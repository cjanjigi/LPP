/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import LPP_Foundations.Frozen.Model.LastPassage
public import LPP_Foundations.Frozen.Model.Quadrant
public import Martin2004.Probability.AffineShape
public import Martin2004.Probability.GaussianBlockComparisonBound
public import Martin2004.Probability.NormalExponentialTails
public import ProbabilityBasics.Probability.SqrtDistanceCLT

@[expose] public section

/-!
# Gaussian comparison of block shapes (Martin 2004, Lemma 4.5)

Martin (2004), Lemma 4.5, is proved here. Let `μ` have bounded support, mean `m` and variance `σ²`,
let `ν k` be the law of the sum of `k` independent copies with shape `G k`, and let `gΦ` be the
shape for standard normal weights. If `r(α) → ∞` and `r(α) √α → 0` as `α ↓ 0`, then
`(G_r(1, α r) / r - m - σ gΦ(1, α r) / √r) / √α → 0`.

* The finite-block estimate (Martin (2004), Lemma 4.2, applied to `ν r` and the image of the
  standard normal law) is in `GaussianBlockComparisonBound.lean`.
* For `σ > 0`, the quantity splits into a term controlled by that estimate, at most
  `2 σ √(1 + α r) ε_r` with `ε_r → 0` (by the central limit theorem with domination), and the
  drift term `m r √α`, which tends to zero. For `σ = 0`, `ν r` is a point mass, the shape is
  `G_r x = r m (x₁ + x₂)`, and the quantity equals `m r √α`.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace LPPDifferentiability

/-! ### Algebra of the quantity -/

/-- The quantity of Martin (2004), Lemma 4.5, is the finite-block error divided by `r √α`, plus the
drift term `m r √α`. The drift comes from the term `r m (1 + α r)` in the shape of the block law. -/
private lemma quantity_split (G g m σ r α : ℝ) (hr : 0 < r) (hα : 0 < α) :
    (G / r - m - σ * g / Real.sqrt r) / Real.sqrt α =
      (G - σ * Real.sqrt r * g - r * m * (1 + α * r)) / (r * Real.sqrt α) +
        m * (r * Real.sqrt α) := by
  obtain ⟨t, ht, rfl⟩ : ∃ t : ℝ, 0 < t ∧ r = t ^ 2 :=
    ⟨Real.sqrt r, Real.sqrt_pos.2 hr, (Real.sq_sqrt hr.le).symm⟩
  obtain ⟨s, hs, rfl⟩ : ∃ s : ℝ, 0 < s ∧ α = s ^ 2 :=
    ⟨Real.sqrt α, Real.sqrt_pos.2 hα, (Real.sq_sqrt hα.le).symm⟩
  rw [Real.sqrt_sq ht.le, Real.sqrt_sq hs.le]
  field_simp
  ring

/-- The constant of the finite-block estimate, divided by `r √α`, is `2 σ √(1 + α r)`. This is the
constant that appears in the proof of Martin (2004), Lemma 4.5. -/
private lemma estimate_constant (σ r α : ℝ) (hr : 0 < r) (hα : 0 < α) :
    2 * Real.sqrt (α * r * (1 + α * r)) * (σ * Real.sqrt r) * (r * Real.sqrt α)⁻¹ =
      2 * σ * Real.sqrt (1 + α * r) := by
  obtain ⟨t, ht, rfl⟩ : ∃ t : ℝ, 0 < t ∧ r = t ^ 2 :=
    ⟨Real.sqrt r, Real.sqrt_pos.2 hr, (Real.sq_sqrt hr.le).symm⟩
  obtain ⟨s, hs, rfl⟩ : ∃ s : ℝ, 0 < s ∧ α = s ^ 2 :=
    ⟨Real.sqrt α, Real.sqrt_pos.2 hα, (Real.sq_sqrt hα.le).symm⟩
  have hroot : Real.sqrt (s ^ 2 * t ^ 2 * (1 + s ^ 2 * t ^ 2)) =
      s * t * Real.sqrt (1 + s ^ 2 * t ^ 2) := by
    rw [show s ^ 2 * t ^ 2 * (1 + s ^ 2 * t ^ 2) = (s * t) ^ 2 * (1 + s ^ 2 * t ^ 2) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  rw [hroot, Real.sqrt_sq ht.le, Real.sqrt_sq hs.le]
  field_simp

/-- Algebra from the finite-block estimate to the bound for the quantity:
`|Q| ≤ 2 σ √(1 + α r) ε + |m| r √α`, in `[0, ∞]`. -/
private lemma quantity_le_of_estimate (G g m σ r α : ℝ) (hσ : 0 ≤ σ) (hr : 0 < r) (hα : 0 < α)
    (ε : ℝ≥0∞)
    (hE : ENNReal.ofReal |G - σ * Real.sqrt r * g - r * m * (1 + α * r)| ≤
      ENNReal.ofReal (2 * Real.sqrt (α * r * (1 + α * r)) * (σ * Real.sqrt r)) * ε) :
    ENNReal.ofReal |(G / r - m - σ * g / Real.sqrt r) / Real.sqrt α| ≤
      ENNReal.ofReal (2 * σ * Real.sqrt (1 + α * r)) * ε +
        ENNReal.ofReal (|m| * (r * Real.sqrt α)) := by
  rw [quantity_split G g m σ r α hr hα]
  have hd : 0 < r * Real.sqrt α := mul_pos hr (Real.sqrt_pos.2 hα)
  have hc : 0 ≤ 2 * Real.sqrt (α * r * (1 + α * r)) * (σ * Real.sqrt r) := by positivity
  have h1 : |(G - σ * Real.sqrt r * g - r * m * (1 + α * r)) / (r * Real.sqrt α) +
        m * (r * Real.sqrt α)| ≤
      |G - σ * Real.sqrt r * g - r * m * (1 + α * r)| * (r * Real.sqrt α)⁻¹ +
        |m| * (r * Real.sqrt α) := by
    refine (abs_add_le _ _).trans (le_of_eq ?_)
    rw [abs_div, abs_of_pos hd, abs_mul, abs_of_pos hd, div_eq_mul_inv]
  refine (ENNReal.ofReal_le_ofReal h1).trans (ENNReal.ofReal_add_le.trans ?_)
  refine add_le_add ?_ le_rfl
  rw [ENNReal.ofReal_mul (abs_nonneg _)]
  calc ENNReal.ofReal |G - σ * Real.sqrt r * g - r * m * (1 + α * r)| *
        ENNReal.ofReal (r * Real.sqrt α)⁻¹
      ≤ (ENNReal.ofReal (2 * Real.sqrt (α * r * (1 + α * r)) * (σ * Real.sqrt r)) * ε) *
          ENNReal.ofReal (r * Real.sqrt α)⁻¹ := mul_le_mul' hE le_rfl
    _ = ENNReal.ofReal (2 * Real.sqrt (α * r * (1 + α * r)) * (σ * Real.sqrt r) *
          (r * Real.sqrt α)⁻¹) * ε := by
        rw [ENNReal.ofReal_mul hc, mul_right_comm]
    _ = ENNReal.ofReal (2 * σ * Real.sqrt (1 + α * r)) * ε := by
        rw [estimate_constant σ r α hr hα]

/-! ### The case of positive variance -/

/-- **Martin (2004), Lemma 4.5, for `σ > 0`.** The finite-block estimate bounds the quantity by
`2 σ √(1 + α r) ε_r + |m| r √α`. Here `ε_r → 0` by the central limit theorem with domination, and
`α r → 0` and `r √α → 0`. -/
private lemma tendsto_of_positive_variance
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (K : ℝ) (hK : ∀ᵐ t ∂μ, |t| ≤ K)
    (m σ : ℝ) (hσ : 0 < σ) (hm : ∫ t : ℝ, t ∂μ = m) (hvar : ∫ t : ℝ, (t - m) ^ 2 ∂μ = σ ^ 2)
    (r : ℝ≥0 → ℕ) (hr1 : ∀ α, 1 ≤ r α)
    (hr : Tendsto (fun α => (r α : ℝ)) (𝓝[>] (0 : ℝ≥0)) atTop)
    (hrα : Tendsto (fun α : ℝ≥0 => (r α : ℝ) * Real.sqrt (α : ℝ)) (𝓝[>] (0 : ℝ≥0)) (𝓝 0))
    (ν : ℕ → Measure ℝ) [∀ k, IsProbabilityMeasure (ν k)]
    (hν : ∀ k, ν k = (Measure.pi (fun _ : Fin k => μ)).map (fun y => ∑ i, y i))
    (G : ℕ → Quadrant → ℝ)
    (hG : ∀ k, ∀ x : Quadrant, Tendsto (fun n : ℕ =>
        (∫ ω : Environment, lastPassage ω 0
          (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
          ∂environmentLaw (ν k)) / (n : ℝ)) atTop (𝓝 (G k x)))
    (gΦ : Quadrant → ℝ)
    (hΦ : ∀ x : Quadrant, Tendsto (fun n : ℕ =>
        (∫ ω : Environment, lastPassage ω 0
          (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
          ∂environmentLaw (gaussianReal 0 1)) / (n : ℝ)) atTop (𝓝 (gΦ x))) :
    Tendsto (fun α : ℝ≥0 =>
      (G (r α) (1, α * (r α : ℝ≥0)) / (r α : ℝ) - m -
        σ * gΦ (1, α * (r α : ℝ≥0)) / Real.sqrt (r α : ℝ)) / Real.sqrt (α : ℝ))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 0) := by
  -- the square-root distance `ε_r` of the normalized block law to the normal law tends to `0`
  set ε : ℕ → ℝ≥0∞ := fun n => ∫⁻ x : ℝ, (ENNReal.ofReal |((ν n).map
      (fun s : ℝ => (s - n * m) / (σ * Real.sqrt n))).real (Iic x) -
        (gaussianReal 0 1).real (Iic x)|) ^ (1 / 2 : ℝ)
  have hε : Tendsto ε atTop (𝓝 0) :=
    sqrt_cdf_distance_sum_law_tendsto_zero μ K hK m σ hσ hm hvar ν hν
  have hr' : Tendsto r (𝓝[>] (0 : ℝ≥0)) atTop := tendsto_natCast_atTop_iff.1 hr
  have hεr : Tendsto (fun α : ℝ≥0 => ε (r α)) (𝓝[>] (0 : ℝ≥0)) (𝓝 0) := hε.comp hr'
  -- `√α → 0` and `α r → 0`
  have hsq : Tendsto (fun α : ℝ≥0 => Real.sqrt (α : ℝ)) (𝓝[>] (0 : ℝ≥0)) (𝓝 0) := by
    exact (Real.continuous_sqrt.tendsto' 0 0 Real.sqrt_zero).comp
      ((NNReal.continuous_coe.tendsto' 0 0 NNReal.coe_zero).mono_left nhdsWithin_le_nhds)
  have hβ : Tendsto (fun α : ℝ≥0 => (α : ℝ) * (r α : ℝ)) (𝓝[>] (0 : ℝ≥0)) (𝓝 0) := by
    have h := hrα.mul hsq
    rw [mul_zero] at h
    refine h.congr fun α => ?_
    calc (r α : ℝ) * Real.sqrt (α : ℝ) * Real.sqrt (α : ℝ) =
          (Real.sqrt (α : ℝ) * Real.sqrt (α : ℝ)) * (r α : ℝ) := by ring
      _ = (α : ℝ) * (r α : ℝ) := by rw [Real.mul_self_sqrt (NNReal.coe_nonneg α)]
  have hβ1 : ∀ᶠ α : ℝ≥0 in 𝓝[>] (0 : ℝ≥0), (α : ℝ) * (r α : ℝ) < 1 :=
    hβ.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  -- the bound for the quantity, with the constant `2 σ √(1 + α r) ≤ 4 σ`
  have hbound : ∀ᶠ α : ℝ≥0 in 𝓝[>] (0 : ℝ≥0),
      ENNReal.ofReal |(G (r α) (1, α * (r α : ℝ≥0)) / (r α : ℝ) - m -
          σ * gΦ (1, α * (r α : ℝ≥0)) / Real.sqrt (r α : ℝ)) / Real.sqrt (α : ℝ)| ≤
        ENNReal.ofReal (4 * σ) * ε (r α) + ENNReal.ofReal (|m| * ((r α : ℝ) * Real.sqrt (α : ℝ))) := by
    filter_upwards [self_mem_nhdsWithin, hβ1] with α hα hβα
    have hα0 : 0 < α := hα
    have hr0 : (0 : ℝ) < (r α : ℝ) := Nat.cast_pos.2 (hr1 α)
    have hpos : 0 < α * (r α : ℝ≥0) := mul_pos hα0 (Nat.cast_pos.2 (hr1 α))
    have hE := block_shape_gaussian_estimate μ K hK m σ hσ hm ν hν G hG gΦ hΦ (r α) (hr1 α)
      (α * (r α : ℝ≥0)) hpos
    have hcast : ((α * (r α : ℝ≥0) : ℝ≥0) : ℝ) = (α : ℝ) * (r α : ℝ) := by simp
    rw [hcast] at hE
    refine (quantity_le_of_estimate _ _ m σ (r α) α hσ.le hr0 (NNReal.coe_pos.2 hα0) (ε (r α))
      hE).trans ?_
    have hw : Real.sqrt (1 + (α : ℝ) * (r α : ℝ)) ≤ 2 :=
      Real.sqrt_le_iff.2 ⟨by norm_num, by nlinarith⟩
    have h4 : 2 * σ * Real.sqrt (1 + (α : ℝ) * (r α : ℝ)) ≤ 4 * σ := by
      nlinarith [mul_le_mul_of_nonneg_left hw hσ.le]
    exact add_le_add (mul_le_mul' (ENNReal.ofReal_le_ofReal h4) le_rfl) le_rfl
  -- the right side tends to `0`
  have hlim : Tendsto (fun α : ℝ≥0 => ENNReal.ofReal (4 * σ) * ε (r α) +
      ENNReal.ofReal (|m| * ((r α : ℝ) * Real.sqrt (α : ℝ)))) (𝓝[>] (0 : ℝ≥0)) (𝓝 0) := by
    have h1 := ENNReal.Tendsto.const_mul hεr (Or.inr ENNReal.ofReal_ne_top :
      _ ∨ ENNReal.ofReal (4 * σ) ≠ ∞)
    have h2 := ENNReal.tendsto_ofReal (hrα.const_mul |m|)
    simpa using h1.add h2
  have hQ := tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) hbound
  -- from the extended-real bound back to the real quantity
  refine (tendsto_zero_iff_abs_tendsto_zero _).2 ?_
  have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hQ
  simpa [Function.comp_def, ENNReal.toReal_ofReal (abs_nonneg _)] using h

/-! ### The case of zero variance -/

/-- **Martin (2004), Lemma 4.5, for `σ = 0`** (direct computation). If the variance is zero, `μ`
is the point mass at `m`, so `ν k` is the point mass at `k m`, the image of the standard normal law
under `t ↦ 0 t + k m`. The affine theorem for expected rates, with `a = 0`, gives
`G k x = k m (x₁ + x₂)`, and the quantity equals `m r √α`. -/
private lemma tendsto_of_zero_variance
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (K : ℝ) (hK : ∀ᵐ t ∂μ, |t| ≤ K)
    (m σ : ℝ) (hσ : σ = 0) (hvar : ∫ t : ℝ, (t - m) ^ 2 ∂μ = σ ^ 2)
    (r : ℝ≥0 → ℕ) (hr1 : ∀ α, 1 ≤ r α)
    (hrα : Tendsto (fun α : ℝ≥0 => (r α : ℝ) * Real.sqrt (α : ℝ)) (𝓝[>] (0 : ℝ≥0)) (𝓝 0))
    (ν : ℕ → Measure ℝ) [∀ k, IsProbabilityMeasure (ν k)]
    (hν : ∀ k, ν k = (Measure.pi (fun _ : Fin k => μ)).map (fun y => ∑ i, y i))
    (G : ℕ → Quadrant → ℝ)
    (hG : ∀ k, ∀ x : Quadrant, Tendsto (fun n : ℕ =>
        (∫ ω : Environment, lastPassage ω 0
          (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
          ∂environmentLaw (ν k)) / (n : ℝ)) atTop (𝓝 (G k x)))
    (gΦ : Quadrant → ℝ)
    (hΦ : ∀ x : Quadrant, Tendsto (fun n : ℕ =>
        (∫ ω : Environment, lastPassage ω 0
          (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
          ∂environmentLaw (gaussianReal 0 1)) / (n : ℝ)) atTop (𝓝 (gΦ x))) :
    Tendsto (fun α : ℝ≥0 =>
      (G (r α) (1, α * (r α : ℝ≥0)) / (r α : ℝ) - m -
        σ * gΦ (1, α * (r α : ℝ≥0)) / Real.sqrt (r α : ℝ)) / Real.sqrt (α : ℝ))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 0) := by
  subst hσ
  have hγ : Integrable (fun t : ℝ => t) (gaussianReal 0 1) :=
    memLp_one_iff_integrable.1 (memLp_id_gaussianReal' 1 ENNReal.one_ne_top)
  -- the variance integrand vanishes almost surely, so `μ` is the point mass at `m`
  have hint : Integrable (fun t : ℝ => (t - m) ^ 2) μ := by
    refine Integrable.of_bound
      (by fun_prop : Continuous fun t : ℝ => (t - m) ^ 2).aestronglyMeasurable
      ((K + |m|) ^ 2) (hK.mono fun t ht => ?_)
    have h1 : |t - m| ≤ K + |m| :=
      abs_le.2 ⟨by linarith [abs_le.1 ht, le_abs_self m], by linarith [abs_le.1 ht, neg_abs_le m]⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc (t - m) ^ 2 = |t - m| ^ 2 := (sq_abs _).symm
      _ ≤ (K + |m|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hae : ∀ᵐ t ∂μ, t = m := by
    have h0 := (integral_eq_zero_iff_of_nonneg (fun t => sq_nonneg (t - m)) hint).1
      (by simpa using hvar)
    filter_upwards [h0] with t ht
    exact sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 ht)
  -- each block law is a point mass: the image of the standard normal law under `t ↦ 0 t + k m`
  have hνk : ∀ k : ℕ, ν k = (gaussianReal 0 1).map (fun t : ℝ => 0 * t + k * m) := by
    intro k
    have hcoord : ∀ᵐ y ∂(Measure.pi (fun _ : Fin k => μ)), ∀ i, y i = m :=
      ae_all_iff.2 fun i =>
        (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin k => μ) (i := i)).eventually hae
    have hsum : (fun y : Fin k → ℝ => ∑ i, y i) =ᵐ[Measure.pi (fun _ : Fin k => μ)]
        fun _ => (k : ℝ) * m := by
      filter_upwards [hcoord] with y hy
      simp [hy]
    have hfun : (fun t : ℝ => 0 * t + (k : ℝ) * m) = fun _ => (k : ℝ) * m := by
      funext t
      simp
    rw [hν k, Measure.map_congr hsum, hfun, Measure.map_const, Measure.map_const]
    simp
  -- the shape of `ν k`
  have hshape : ∀ (k : ℕ) (x : Quadrant),
      G k x = 0 * gΦ x + k * m * ((x.1 : ℝ) + (x.2 : ℝ)) := fun k =>
    expected_rate_affine_image (gaussianReal 0 1) (ν k) hγ 0 (k * m) le_rfl (hνk k) gΦ (G k) hΦ
      (hG k)
  -- the quantity equals `m r √α`
  have hQ : ∀ᶠ α : ℝ≥0 in 𝓝[>] (0 : ℝ≥0), (G (r α) (1, α * (r α : ℝ≥0)) / (r α : ℝ) - m -
        0 * gΦ (1, α * (r α : ℝ≥0)) / Real.sqrt (r α : ℝ)) / Real.sqrt (α : ℝ) =
      m * ((r α : ℝ) * Real.sqrt (α : ℝ)) := by
    filter_upwards [self_mem_nhdsWithin] with α hα
    have hα0 : 0 < (α : ℝ) := NNReal.coe_pos.2 hα
    have hr0 : (0 : ℝ) < (r α : ℝ) := Nat.cast_pos.2 (hr1 α)
    rw [quantity_split _ _ m 0 (r α) α hr0 hα0, hshape (r α)]
    simp only [zero_mul, zero_add, NNReal.coe_one, NNReal.coe_mul, NNReal.coe_natCast]
    ring
  have hlim := hrα.const_mul m
  rw [mul_zero] at hlim
  exact hlim.congr' (hQ.mono fun α h => h.symm)

/-! ### Martin, Lemma 4.5 -/

/-- **Martin (2004), Lemma 4.5.** For a law `μ` with bounded support, mean `m` and variance `σ²`,
with `G k` the shape of the law of the sum of `k` independent copies and `gΦ` the shape for
standard normal weights, if `r(α) → ∞` and `r(α) √α → 0` as `α ↓ 0`, then
`(G_r(1, α r) / r - m - σ gΦ(1, α r) / √r) / √α → 0`. The case `σ > 0` uses Lemma 4.2 and the
central limit theorem with domination; the case `σ = 0` is a direct computation. -/
theorem martin_lemma_4_5
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (K : ℝ) (hK : ∀ᵐ t ∂μ, |t| ≤ K)
    (r : ℝ≥0 → ℕ) (hr1 : ∀ α, 1 ≤ r α)
    (hr : Tendsto (fun α => (r α : ℝ)) (𝓝[>] (0 : ℝ≥0)) atTop)
    (hrα : Tendsto (fun α : ℝ≥0 => (r α : ℝ) * Real.sqrt (α : ℝ)) (𝓝[>] (0 : ℝ≥0)) (𝓝 0))
    (ν : ℕ → Measure ℝ) [∀ k, IsProbabilityMeasure (ν k)]
    (hν : ∀ k, ν k = (Measure.pi (fun _ : Fin k => μ)).map (fun y => ∑ i, y i))
    (G : ℕ → Quadrant → ℝ)
    (hG : ∀ k, ∀ x : Quadrant, Tendsto (fun n : ℕ =>
        (∫ ω : Environment, lastPassage ω 0
          (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
          ∂environmentLaw (ν k)) / (n : ℝ)) atTop (𝓝 (G k x)))
    (gΦ : Quadrant → ℝ)
    (hΦ : ∀ x : Quadrant, Tendsto (fun n : ℕ =>
        (∫ ω : Environment, lastPassage ω 0
          (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
          ∂environmentLaw (gaussianReal 0 1)) / (n : ℝ)) atTop (𝓝 (gΦ x))) :
    Tendsto (fun α : ℝ≥0 =>
      (G (r α) (1, α * (r α : ℝ≥0)) / (r α : ℝ) - (∫ t : ℝ, t ∂μ) -
        Real.sqrt (∫ t : ℝ, (t - ∫ s : ℝ, s ∂μ) ^ 2 ∂μ) *
          gΦ (1, α * (r α : ℝ≥0)) / Real.sqrt (r α : ℝ)) / Real.sqrt (α : ℝ))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 0) := by
  have hv0 : 0 ≤ ∫ t : ℝ, (t - ∫ s : ℝ, s ∂μ) ^ 2 ∂μ := integral_nonneg fun t => sq_nonneg _
  have hvar : ∫ t : ℝ, (t - ∫ s : ℝ, s ∂μ) ^ 2 ∂μ =
      Real.sqrt (∫ t : ℝ, (t - ∫ s : ℝ, s ∂μ) ^ 2 ∂μ) ^ 2 := (Real.sq_sqrt hv0).symm
  rcases (Real.sqrt_nonneg (∫ t : ℝ, (t - ∫ s : ℝ, s ∂μ) ^ 2 ∂μ)).eq_or_lt with h0 | hpos
  · exact tendsto_of_zero_variance μ K hK _ _ h0.symm hvar r hr1 hrα ν hν G hG gΦ hΦ
  · exact tendsto_of_positive_variance μ K hK _ _ hpos rfl hvar r hr1 hr hrα ν hν G hG gΦ hΦ

end LPPDifferentiability
