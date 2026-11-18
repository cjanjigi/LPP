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
public import Martin2004.Probability.NormalExponentialTails
public import Martin2004.Probability.ShapeComparison
public import ProbabilityBasics.Probability.SqrtCdfDistance
import LPP_Foundations.Probability.PassageMeanBounds

@[expose] public section

/-!
# Finite-block estimate for the Gaussian comparison (Martin 2004, Lemma 4.5)

This is the finite-block step in the proof of Martin (2004), Lemma 4.5. Let `ν r` be the law of
the sum of `r` independent copies of a bounded law `μ` with mean `m` and standard deviation
`σ > 0`, and let `N_r` be the law of `σ √r Z + r m` for a standard normal `Z`. Both have mean
`r m`. Martin (2004), Lemma 4.2, compares the shapes of `ν r` and `N_r` at `(1, β)`. The shape of
`N_r` is `σ √r gΦ + r m (x₁ + x₂)` by the affine-image theorem, and the drift term
`r m (x₁ + x₂)` is kept. The change of variables `s = σ √r u + r m` turns the square-root distance
of `ν r` and `N_r` into `σ √r` times the square-root distance of the normalized law and the
standard normal law.

* `block_shape_gaussian_estimate`: for `r ≥ 1` and `β > 0`,
  `|G_r(1, β) - σ √r gΦ(1, β) - r m (1 + β)| ≤ 2 √(β (1 + β)) σ √r ε_r` in `[0, ∞]`, where `ε_r` is
  the square-root distance of the normalized sum law to the standard normal law.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace LPPDifferentiability

/-! ### Change of variables under `s = a u + b` -/

/-- The integral over `s` of `f s` is `a` times the integral over `u` of `f (a u + b)`, for
`a > 0`. -/
private lemma lintegral_affine (f : ℝ → ℝ≥0∞) {a : ℝ} (ha : 0 < a) (b : ℝ) :
    ∫⁻ s, f s = ENNReal.ofReal a * ∫⁻ u, f (a * u + b) := by
  rw [← lintegral_add_right_eq_self f b]
  let e : ℝ ≃ᵐ ℝ := (Homeomorph.mulLeft₀ a ha.ne').toMeasurableEquiv
  have h2 := lintegral_map_equiv (μ := (volume : Measure ℝ)) (fun s => f (s + b)) e
  have hmap : Measure.map e (volume : Measure ℝ) = ENNReal.ofReal |a⁻¹| • volume :=
    Real.map_volume_mul_left ha.ne'
  rw [hmap, lintegral_smul_measure] at h2
  have h3 : ∫⁻ u, f (e u + b) = ∫⁻ u, f (a * u + b) := rfl
  rw [h3] at h2
  rw [← h2, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul ha.le, abs_of_pos (inv_pos.2 ha),
    mul_inv_cancel₀ ha.ne', ENNReal.ofReal_one, one_mul]

/-- The same change of variables for the integral over a measurable set `S`; the domain on the
right is the preimage of `S`. -/
private lemma lintegral_set_affine (f : ℝ → ℝ≥0∞) (S : Set ℝ) (hS : MeasurableSet S)
    {a : ℝ} (ha : 0 < a) (b : ℝ) :
    ∫⁻ s in S, f s = ENNReal.ofReal a *
      ∫⁻ u in (fun u : ℝ => a * u + b) ⁻¹' S, f (a * u + b) := by
  have hpre : MeasurableSet ((fun u : ℝ => a * u + b) ⁻¹' S) := hS.preimage (by fun_prop)
  rw [← lintegral_indicator hS, lintegral_affine _ ha b, ← lintegral_indicator hpre]
  congr 1

/-! ### Distribution functions under the affine change -/

/-- The mass of `(-∞, a u + b]` for the image of the standard normal law under `t ↦ a t + b`
equals the standard normal mass of `(-∞, u]`. -/
private lemma map_affine_Iic (γ : Measure ℝ) {a : ℝ} (ha : 0 < a) (b u : ℝ) :
    (γ.map (fun t : ℝ => a * t + b)) (Iic (a * u + b)) = γ (Iic u) := by
  rw [Measure.map_apply (by fun_prop) measurableSet_Iic]
  congr 1
  ext t
  simp only [mem_preimage, mem_Iic]
  constructor
  · intro h
    by_contra hc
    nlinarith [mul_lt_mul_of_pos_left (not_le.1 hc) ha]
  · intro h
    nlinarith

/-- The upper tail version of `map_affine_Iic`. -/
private lemma map_affine_Ioi (γ : Measure ℝ) {a : ℝ} (ha : 0 < a) (b u : ℝ) :
    (γ.map (fun t : ℝ => a * t + b)) (Ioi (a * u + b)) = γ (Ioi u) := by
  rw [Measure.map_apply (by fun_prop) measurableSet_Ioi]
  congr 1
  ext t
  simp only [mem_preimage, mem_Ioi]
  constructor
  · intro h
    by_contra hc
    nlinarith [mul_le_mul_of_nonneg_left (not_lt.1 hc) ha.le]
  · intro h
    nlinarith [mul_lt_mul_of_pos_left h ha]

/-- The distribution function of the law of `(s - b) / a` at `u` is that of the law at `a u + b`. -/
private lemma real_Iic_map_normalize (ν : Measure ℝ) {a : ℝ} (ha : 0 < a) (b u : ℝ) :
    (ν.map fun s : ℝ => (s - b) / a).real (Iic u) = ν.real (Iic (a * u + b)) := by
  rw [measureReal_def, measureReal_def,
    Measure.map_apply (by fun_prop : Measurable fun s : ℝ => (s - b) / a) measurableSet_Iic]
  congr 2
  ext s
  simp only [mem_preimage, mem_Iic, div_le_iff₀ ha]
  constructor <;> intro h <;> linarith

/-- The distribution function of the affine image of `γ` at `a u + b` is that of `γ` at `u`. -/
private lemma real_Iic_map_affine (γ : Measure ℝ) {a : ℝ} (ha : 0 < a) (b u : ℝ) :
    (γ.map (fun t : ℝ => a * t + b)).real (Iic (a * u + b)) = γ.real (Iic u) := by
  rw [measureReal_def, measureReal_def, map_affine_Iic γ ha b u]

/-- After the change of variables `s = a u + b`, the square-root distance of `ν` and the image of
`γ` is `a` times that of the normalized law of `ν` and `γ`. -/
private lemma sqrt_distance_affine (ν γ : Measure ℝ) {a : ℝ} (ha : 0 < a) (b : ℝ) :
    sqrtCdfDistance ν (γ.map (fun t : ℝ => a * t + b)) =
      ENNReal.ofReal a * sqrtCdfDistance (ν.map (fun s : ℝ => (s - b) / a)) γ := by
  unfold sqrtCdfDistance
  rw [lintegral_affine _ ha b]
  congr 1
  refine lintegral_congr fun u => ?_
  rw [real_Iic_map_normalize ν ha b u, real_Iic_map_affine γ ha b u]

/-! ### Square-root tails (the hypotheses of Martin (2004), Lemma 4.2) -/

/-- A law concentrated on `[-C, C]` has lower tail at most `1` on `[-C, C]` and `0` below it. -/
lemma lower_tail_le_indicator {ρ : Measure ℝ} [IsProbabilityMeasure ρ] {C : ℝ}
    (h : ∀ᵐ t ∂ρ, |t| ≤ C) {t : ℝ} (ht : t < 0) :
    ρ (Iic t) ^ (1 / 2 : ℝ) ≤ (Icc (-C) C).indicator (fun _ => (1 : ℝ≥0∞)) t := by
  have hC : 0 ≤ C := by
    obtain ⟨x, hx⟩ := h.exists
    exact (abs_nonneg x).trans hx
  by_cases hmem : t ∈ Icc (-C) C
  · rw [indicator_of_mem hmem]
    exact ENNReal.rpow_le_one prob_le_one (by norm_num)
  · have htC : t < -C := by
      simp only [mem_Icc, not_and_or, not_le] at hmem
      rcases hmem with h1 | h1
      · exact h1
      · linarith
    have h0 : ρ (Iic t) = 0 := by
      refine measure_mono_null (t := {x | ¬ |x| ≤ C}) (fun x hx => ?_) (ae_iff.1 h)
      simp only [mem_ofPred_eq, not_le]
      have hxt : x ≤ t := hx
      linarith [neg_le_abs x]
    rw [h0, ENNReal.zero_rpow_of_pos (by norm_num)]
    exact zero_le

/-- The upper tail version of `lower_tail_le_indicator`. -/
lemma upper_tail_le_indicator {ρ : Measure ℝ} [IsProbabilityMeasure ρ] {C : ℝ}
    (h : ∀ᵐ t ∂ρ, |t| ≤ C) {t : ℝ} (ht : 0 < t) :
    ρ (Ioi t) ^ (1 / 2 : ℝ) ≤ (Icc (-C) C).indicator (fun _ => (1 : ℝ≥0∞)) t := by
  have hC : 0 ≤ C := by
    obtain ⟨x, hx⟩ := h.exists
    exact (abs_nonneg x).trans hx
  by_cases hmem : t ∈ Icc (-C) C
  · rw [indicator_of_mem hmem]
    exact ENNReal.rpow_le_one prob_le_one (by norm_num)
  · have htC : C < t := by
      simp only [mem_Icc, not_and_or, not_le] at hmem
      rcases hmem with h1 | h1
      · linarith
      · exact h1
    have h0 : ρ (Ioi t) = 0 := by
      refine measure_mono_null (t := {x | ¬ |x| ≤ C}) (fun x hx => ?_) (ae_iff.1 h)
      simp only [mem_ofPred_eq, not_le]
      have hxt : t < x := hx
      linarith [le_abs_self x]
    rw [h0, ENNReal.zero_rpow_of_pos (by norm_num)]
    exact zero_le

/-- A law with bounded support has finite integrated square-root tails, in the sense of Martin
(2004), (2.6) and (2.7): the integrands are at most `1` on `[-C, C]` and vanish elsewhere. -/
lemma sqrt_tails_of_bounded (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (C : ℝ)
    (h : ∀ᵐ t ∂ρ, |t| ≤ C) :
    (∫⁻ t in Iio (0 : ℝ), (ρ (Iic t)) ^ (1 / 2 : ℝ)) < ∞ ∧
      (∫⁻ t in Ioi (0 : ℝ), (ρ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞ := by
  have hfin : ∫⁻ t, (Icc (-C) C).indicator (fun _ => (1 : ℝ≥0∞)) t < ∞ := by
    rw [lintegral_indicator_const measurableSet_Icc, Real.volume_Icc]
    exact ENNReal.mul_lt_top ENNReal.one_lt_top ENNReal.ofReal_lt_top
  refine ⟨lt_of_le_of_lt
      ((setLIntegral_mono' measurableSet_Iio fun t ht => lower_tail_le_indicator h ht).trans
        (setLIntegral_le_lintegral _ _)) hfin,
    lt_of_le_of_lt
      ((setLIntegral_mono' measurableSet_Ioi fun t ht => upper_tail_le_indicator h ht).trans
        (setLIntegral_le_lintegral _ _)) hfin⟩

/-- Finiteness of the lower tail integral over `(-∞, 0)` gives it over `(-∞, c)` for every `c`. -/
private lemma sqrt_tail_neg_shift (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (c : ℝ)
    (h : (∫⁻ t in Iio (0 : ℝ), (ρ (Iic t)) ^ (1 / 2 : ℝ)) < ∞) :
    (∫⁻ t in Iio c, (ρ (Iic t)) ^ (1 / 2 : ℝ)) < ∞ := by
  have hsub : Iio c ⊆ Iio 0 ∪ Icc 0 |c| := by
    intro t ht
    by_cases h0 : t < 0
    · exact Or.inl h0
    · exact Or.inr ⟨not_lt.1 h0, (le_of_lt ht).trans (le_abs_self c)⟩
  have hbd : (∫⁻ t in Icc 0 |c|, (ρ (Iic t)) ^ (1 / 2 : ℝ)) < ∞ := by
    calc ∫⁻ t in Icc 0 |c|, (ρ (Iic t)) ^ (1 / 2 : ℝ) ≤ ∫⁻ _ in Icc (0 : ℝ) |c|, (1 : ℝ≥0∞) :=
          setLIntegral_mono' measurableSet_Icc fun t _ =>
            ENNReal.rpow_le_one prob_le_one (by norm_num)
      _ < ∞ := by
          rw [setLIntegral_const, Real.volume_Icc]
          exact ENNReal.mul_lt_top ENNReal.one_lt_top ENNReal.ofReal_lt_top
  calc ∫⁻ t in Iio c, (ρ (Iic t)) ^ (1 / 2 : ℝ)
      ≤ ∫⁻ t in Iio 0 ∪ Icc 0 |c|, (ρ (Iic t)) ^ (1 / 2 : ℝ) := lintegral_mono_set hsub
    _ ≤ (∫⁻ t in Iio 0, (ρ (Iic t)) ^ (1 / 2 : ℝ)) +
          ∫⁻ t in Icc 0 |c|, (ρ (Iic t)) ^ (1 / 2 : ℝ) := lintegral_union_le _ _ _
    _ < ∞ := ENNReal.add_lt_top.2 ⟨h, hbd⟩

/-- Finiteness of the upper tail integral over `(0, ∞)` gives it over `(c, ∞)` for every `c`. -/
private lemma sqrt_tail_pos_shift (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (c : ℝ)
    (h : (∫⁻ t in Ioi (0 : ℝ), (ρ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞) :
    (∫⁻ t in Ioi c, (ρ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞ := by
  have hsub : Ioi c ⊆ Ioi 0 ∪ Icc (-|c|) 0 := by
    intro t ht
    by_cases h0 : 0 < t
    · exact Or.inl h0
    · exact Or.inr ⟨(neg_abs_le c).trans (le_of_lt ht), not_lt.1 h0⟩
  have hbd : (∫⁻ t in Icc (-|c|) 0, (ρ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞ := by
    calc ∫⁻ t in Icc (-|c|) 0, (ρ (Ioi t)) ^ (1 / 2 : ℝ) ≤ ∫⁻ _ in Icc (-|c|) (0 : ℝ), (1 : ℝ≥0∞) :=
          setLIntegral_mono' measurableSet_Icc fun t _ =>
            ENNReal.rpow_le_one prob_le_one (by norm_num)
      _ < ∞ := by
          rw [setLIntegral_const, Real.volume_Icc]
          exact ENNReal.mul_lt_top ENNReal.one_lt_top ENNReal.ofReal_lt_top
  calc ∫⁻ t in Ioi c, (ρ (Ioi t)) ^ (1 / 2 : ℝ)
      ≤ ∫⁻ t in Ioi 0 ∪ Icc (-|c|) 0, (ρ (Ioi t)) ^ (1 / 2 : ℝ) := lintegral_mono_set hsub
    _ ≤ (∫⁻ t in Ioi 0, (ρ (Ioi t)) ^ (1 / 2 : ℝ)) +
          ∫⁻ t in Icc (-|c|) 0, (ρ (Ioi t)) ^ (1 / 2 : ℝ) := lintegral_union_le _ _ _
    _ < ∞ := ENNReal.add_lt_top.2 ⟨h, hbd⟩

/-- The image of the standard normal law under `t ↦ a t + b` (`a > 0`) has finite integrated
square-root tails: the change of variables moves the ray `(-∞, 0)` to `(-∞, -b / a)`, where the
standard normal tail integral is finite by the shift lemma. -/
private lemma sqrt_tails_affine_gaussian {a : ℝ} (ha : 0 < a) (b : ℝ) :
    (∫⁻ t in Iio (0 : ℝ), ((gaussianReal 0 1).map (fun t : ℝ => a * t + b)) (Iic t) ^
        (1 / 2 : ℝ)) < ∞ ∧
      (∫⁻ t in Ioi (0 : ℝ), ((gaussianReal 0 1).map (fun t : ℝ => a * t + b)) (Ioi t) ^
        (1 / 2 : ℝ)) < ∞ := by
  obtain ⟨hneg, hpos⟩ := gaussianReal_sqrt_tails
  constructor
  · rw [lintegral_set_affine _ (Iio 0) measurableSet_Iio ha b]
    have hset : (fun u : ℝ => a * u + b) ⁻¹' Iio 0 = Iio (-b / a) := by
      ext u
      simp only [mem_preimage, mem_Iio, lt_div_iff₀ ha]
      constructor <;> intro h <;> linarith
    rw [hset]
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (lt_of_le_of_lt (le_of_eq ?_) (sqrt_tail_neg_shift (gaussianReal 0 1) (-b / a) hneg))
    refine setLIntegral_congr_fun measurableSet_Iio fun u _ => ?_
    simp only [map_affine_Iic _ ha b u]
  · rw [lintegral_set_affine _ (Ioi 0) measurableSet_Ioi ha b]
    have hset : (fun u : ℝ => a * u + b) ⁻¹' Ioi 0 = Ioi (-b / a) := by
      ext u
      simp only [mem_preimage, mem_Ioi, div_lt_iff₀ ha]
      constructor <;> intro h <;> linarith
    rw [hset]
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (lt_of_le_of_lt (le_of_eq ?_) (sqrt_tail_pos_shift (gaussianReal 0 1) (-b / a) hpos))
    refine setLIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    simp only [map_affine_Ioi _ ha b u]

/-! ### Mean and support of the block sum -/

/-- The sum of `k` independent copies of a law with mean `m` has mean `k m`. -/
private lemma integral_sum_law (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ) (m : ℝ) (hm : ∫ t : ℝ, t ∂μ = m) (k : ℕ) (ρ : Measure ℝ)
    (hρ : ρ = (Measure.pi (fun _ : Fin k => μ)).map (fun y => ∑ i, y i)) :
    ∫ s : ℝ, s ∂ρ = k * m := by
  have hsum : Measurable (fun y : Fin k → ℝ => ∑ i, y i) :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  rw [hρ, integral_map (f := fun y : ℝ => y) hsum.aemeasurable aestronglyMeasurable_id,
    integral_finsetSum _ fun i _ => integrable_eval (μ := fun _ : Fin k => μ) hμ]
  have hcoord : ∀ i : Fin k, ∫ y : Fin k → ℝ, y i ∂(Measure.pi (fun _ : Fin k => μ)) = m := by
    intro i
    rw [integral_comp_eval (μ := fun _ : Fin k => μ) (f := fun t : ℝ => t)
      aestronglyMeasurable_id, hm]
  simp [hcoord]

/-- The sum of `k` independent copies of a law concentrated on `[-K, K]` is concentrated on
`[-k K, k K]`. -/
lemma abs_sum_law_le (μ : Measure ℝ) [IsProbabilityMeasure μ] (K : ℝ)
    (hK : ∀ᵐ t ∂μ, |t| ≤ K) (k : ℕ) (ρ : Measure ℝ)
    (hρ : ρ = (Measure.pi (fun _ : Fin k => μ)).map (fun y => ∑ i, y i)) :
    ∀ᵐ s ∂ρ, |s| ≤ k * K := by
  have hsum : Measurable (fun y : Fin k → ℝ => ∑ i, y i) :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  rw [hρ]
  refine (ae_map_iff hsum.aemeasurable (measurableSet_le (by fun_prop) (by fun_prop))).2 ?_
  have hcoord : ∀ i : Fin k, ∀ᵐ y ∂(Measure.pi (fun _ : Fin k => μ)), |y i| ≤ K :=
    fun i => (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin k => μ) (i := i)).eventually hK
  filter_upwards [ae_all_iff.2 hcoord] with y hy
  calc |∑ i, y i| ≤ ∑ i, |y i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin k, K := Finset.sum_le_sum fun i _ => hy i
    _ = k * K := by simp

/-- The image of the standard normal law under `t ↦ a t + b` has mean `b`. -/
private lemma integral_map_affine_gaussian (a b : ℝ) :
    ∫ t : ℝ, t ∂((gaussianReal 0 1).map (fun t : ℝ => a * t + b)) = b := by
  have hγ : Integrable (fun t : ℝ => t) (gaussianReal 0 1) :=
    memLp_one_iff_integrable.1 (memLp_id_gaussianReal' 1 ENNReal.one_ne_top)
  rw [integral_map (f := fun y : ℝ => y)
    (by fun_prop : Measurable (fun t : ℝ => a * t + b)).aemeasurable aestronglyMeasurable_id,
    integral_add (hγ.const_mul a) (integrable_const b), integral_const_mul, integral_id_gaussianReal]
  simp

/-! ### The finite-block estimate -/

/-- **Finite-block estimate for Martin (2004), Lemma 4.5.** For a law `μ` with bounded support,
mean `m` and standard deviation `σ > 0`, with `ν k` the law of the sum of `k` independent copies,
every `r ≥ 1` and `β > 0`:
`|G_r(1, β) - σ √r gΦ(1, β) - r m (1 + β)| ≤ 2 √(β (1 + β)) σ √r ε_r`, where `ε_r` is the
square-root distance between the law of `(S_r - r m) / (σ √r)` and the standard normal law. The
right side is in `[0, ∞]`. -/
theorem block_shape_gaussian_estimate
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (K : ℝ) (hK : ∀ᵐ t ∂μ, |t| ≤ K)
    (m σ : ℝ) (hσ : 0 < σ) (hm : ∫ t : ℝ, t ∂μ = m)
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
          ∂environmentLaw (gaussianReal 0 1)) / (n : ℝ)) atTop (𝓝 (gΦ x)))
    (r : ℕ) (hr : 1 ≤ r) (β : ℝ≥0) (hβ : 0 < β) :
    ENNReal.ofReal |G r (1, β) - σ * Real.sqrt r * gΦ (1, β) - r * m * (1 + (β : ℝ))| ≤
      ENNReal.ofReal (2 * Real.sqrt ((β : ℝ) * (1 + (β : ℝ))) * (σ * Real.sqrt r)) *
        sqrtCdfDistance ((ν r).map (fun s : ℝ => (s - r * m) / (σ * Real.sqrt r)))
          (gaussianReal 0 1) := by
  have hμ := integrable_id_of_ae_abs_le μ K hK
  have hγ : Integrable (fun t : ℝ => t) (gaussianReal 0 1) :=
    memLp_one_iff_integrable.1 (memLp_id_gaussianReal' 1 ENNReal.one_ne_top)
  have ha : 0 < σ * Real.sqrt r := mul_pos hσ (Real.sqrt_pos.2 (Nat.cast_pos.2 hr))
  -- the comparison law `N_r`, the image of the standard normal law
  obtain ⟨N, hN⟩ : ∃ N : Measure ℝ,
      N = (gaussianReal 0 1).map (fun t : ℝ => σ * Real.sqrt r * t + r * m) := ⟨_, rfl⟩
  have : IsProbabilityMeasure N := by
    rw [hN]
    infer_instance
  -- the square-root tails of both laws
  obtain ⟨hneg₁, hpos₁⟩ := sqrt_tails_of_bounded (ν r) (r * K) (abs_sum_law_le μ K hK r (ν r) (hν r))
  obtain ⟨hneg₂, hpos₂⟩ := sqrt_tails_affine_gaussian ha (r * m)
  rw [← hN] at hneg₂ hpos₂
  -- the shape of `N_r`, with the drift term kept
  have hshape : ∀ x : Quadrant, Tendsto (fun n : ℕ =>
      (∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) ∂environmentLaw N) / (n : ℝ))
      atTop (𝓝 (σ * Real.sqrt r * gΦ x + r * m * ((x.1 : ℝ) + (x.2 : ℝ)))) :=
    fun x => tendsto_expected_rate_affine_image (gaussianReal 0 1) N hγ (σ * Real.sqrt r) (r * m)
      ha.le hN x (gΦ x) (hΦ x)
  have h42 := martin_lemma_4_2 (ν r) N hneg₁ hpos₁ hneg₂ hpos₂ (G r)
    (fun x => σ * Real.sqrt r * gΦ x + r * m * ((x.1 : ℝ) + (x.2 : ℝ))) (hG r) hshape β hβ
  -- both means are `r m`, so the mean term of Lemma 4.2 vanishes
  have hmean₁ : ∫ t : ℝ, t ∂(ν r) = r * m := integral_sum_law μ hμ m hm r (ν r) (hν r)
  have hmean₂ : ∫ t : ℝ, t ∂N = r * m := by
    rw [hN]
    exact integral_map_affine_gaussian _ _
  rw [hmean₁, hmean₂, sub_self, mul_zero, sub_zero, hN] at h42
  change _ ≤ _ * sqrtCdfDistance (ν r)
    ((gaussianReal 0 1).map (fun t : ℝ => σ * Real.sqrt r * t + r * m)) at h42
  rw [sqrt_distance_affine (ν r) (gaussianReal 0 1) ha] at h42
  have hlhs : G r (1, β) - σ * Real.sqrt r * gΦ (1, β) - r * m * (1 + (β : ℝ)) =
      G r (1, β) - (σ * Real.sqrt r * gΦ (1, β) + r * m * (((1 : ℝ≥0) : ℝ) + (β : ℝ))) := by
    simp only [NNReal.coe_one]
    ring
  rw [hlhs]
  have hc : (0 : ℝ) ≤ 2 * Real.sqrt ((β : ℝ) * (1 + (β : ℝ))) := by positivity
  refine h42.trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul hc, mul_assoc]

end LPPDifferentiability
