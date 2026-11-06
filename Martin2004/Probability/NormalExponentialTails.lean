/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.ExponentialLaw
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Probability.Distributions.Gamma
public import Mathlib.Probability.CDF
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The standard normal law and Exp(1) satisfy the integrated square-root tails

The statements check Martin (2004), conditions (2.6) and (2.7) of Theorem 2.4,
and the means and variances used with them. The statements are for the Mathlib laws
`gaussianReal 0 1` (standard normal) and `expMeasure 1` (Exp(1)).

The normal tails are bounded by Chernoff bounds, so their square roots are
bounded by `exp (-t^2/4)`, which is integrable. The Exp(1) tails are explicit:
the lower tail is zero below `0`, and the upper tail is `exp (-t)` for
`t >= 0`. The Exp(1) moments are Gamma-function integrals against `exp (-x)`.
-/

public section

open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal

namespace LPPDifferentiability

/-- The moment generating function of the standard normal law at `s` is `exp (s^2/2)`. -/
private lemma mgf_gaussian_zero_one (s : ℝ) :
    mgf id (gaussianReal 0 1) s = Real.exp (s ^ 2 / 2) := by
  rw [mgf_id_gaussianReal]
  simp

/-- Upper Chernoff bound for the standard normal law: for `t >= 0`, the mass of
`[t, infinity)` is at most `exp (-t^2/2)`. -/
private lemma gaussian_Ici_le {t : ℝ} (ht : 0 ≤ t) :
    gaussianReal 0 1 (Ici t) ≤ ENNReal.ofReal (Real.exp (-(t ^ 2) / 2)) := by
  have hint : Integrable (fun ω : ℝ => Real.exp (t * id ω)) (gaussianReal 0 1) :=
    integrable_exp_mul_gaussianReal t
  have h := measure_ge_le_exp_mul_mgf (μ := gaussianReal 0 1) (X := id) (t := t) t ht hint
  rw [mgf_gaussian_zero_one] at h
  have hset : gaussianReal 0 1 (Ici t) = ENNReal.ofReal ((gaussianReal 0 1).real (Ici t)) := by
    rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top (gaussianReal 0 1) (Ici t))]
  have hexp : Real.exp (-t * t) * Real.exp (t ^ 2 / 2) = Real.exp (-(t ^ 2) / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hset]
  apply ENNReal.ofReal_le_ofReal
  exact h.trans (le_of_eq hexp)

/-- Lower Chernoff bound for the standard normal law: for `t <= 0`, the mass of
`(-infinity, t]` is at most `exp (-t^2/2)`. -/
private lemma gaussian_Iic_le {t : ℝ} (ht : t ≤ 0) :
    gaussianReal 0 1 (Iic t) ≤ ENNReal.ofReal (Real.exp (-(t ^ 2) / 2)) := by
  have h := measure_le_le_exp_mul_mgf (μ := gaussianReal 0 1) (X := id) (t := t) t ht
    (integrable_exp_mul_gaussianReal t)
  rw [mgf_gaussian_zero_one] at h
  have hset : gaussianReal 0 1 (Iic t) = ENNReal.ofReal ((gaussianReal 0 1).real (Iic t)) := by
    rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top (gaussianReal 0 1) (Iic t))]
  have hexp : Real.exp (-t * t) * Real.exp (t ^ 2 / 2) = Real.exp (-(t ^ 2) / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hset]
  apply ENNReal.ofReal_le_ofReal
  exact h.trans (le_of_eq hexp)

/-- The square root of the Gaussian Chernoff bound is `exp (-t^2/4)`. -/
private lemma sqrt_gaussian_bound (t : ℝ) :
    ENNReal.ofReal (Real.exp (-(t ^ 2) / 2)) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (Real.exp (-(t ^ 2) / 4)) := by
  rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_nonneg (-(t ^ 2) / 2))
    (by norm_num : (0 : ℝ) ≤ 1 / 2), ← Real.exp_mul,
    show -(t ^ 2) / 2 * (1 / 2 : ℝ) = -(t ^ 2) / 4 by ring]

/-- The function `t ↦ exp (-t^2/4)` is integrable on the real line. -/
private lemma integrable_exp_neg_sq_quarter :
    Integrable (fun t : ℝ => Real.exp (-(t ^ 2) / 4)) := by
  refine (integrable_exp_neg_mul_sq (b := 1 / 4) (by norm_num)).congr
    (Eventually.of_forall fun t => ?_)
  show Real.exp (-(1 / 4) * t ^ 2) = Real.exp (-(t ^ 2) / 4)
  congr 1
  ring

/-- Standard normal law, lower integrated square-root tail (Martin condition (2.7)). -/
private lemma gaussian_neg_sqrt_tail_lt_top :
    (∫⁻ t in Iio (0 : ℝ), (gaussianReal 0 1 (Iic t)) ^ (1 / 2 : ℝ)) < ∞ := by
  have hfin : ∫⁻ t in Iio (0 : ℝ), ENNReal.ofReal (Real.exp (-(t ^ 2) / 4)) < ∞ :=
    (integrable_exp_neg_sq_quarter.restrict (s := Iio 0)).lintegral_lt_top
  have key : ∀ t ∈ Iio (0 : ℝ),
      gaussianReal 0 1 (Iic t) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (Real.exp (-(t ^ 2) / 4)) := by
    intro t ht
    have ht' : t ≤ 0 := (Set.mem_Iio.1 ht).le
    calc gaussianReal 0 1 (Iic t) ^ (1 / 2 : ℝ)
        ≤ ENNReal.ofReal (Real.exp (-(t ^ 2) / 2)) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow (gaussian_Iic_le ht') (by norm_num)
      _ = ENNReal.ofReal (Real.exp (-(t ^ 2) / 4)) := sqrt_gaussian_bound t
  exact lt_of_le_of_lt (setLIntegral_mono' measurableSet_Iio key) hfin

/-- Standard normal law, upper integrated square-root tail (Martin condition (2.6)). -/
private lemma gaussian_pos_sqrt_tail_lt_top :
    (∫⁻ t in Ioi (0 : ℝ), (gaussianReal 0 1 (Ioi t)) ^ (1 / 2 : ℝ)) < ∞ := by
  have hfin : ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(t ^ 2) / 4)) < ∞ :=
    (integrable_exp_neg_sq_quarter.restrict (s := Ioi 0)).lintegral_lt_top
  have key : ∀ t ∈ Ioi (0 : ℝ),
      gaussianReal 0 1 (Ioi t) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (Real.exp (-(t ^ 2) / 4)) := by
    intro t ht
    have ht' : 0 ≤ t := (Set.mem_Ioi.1 ht).le
    calc gaussianReal 0 1 (Ioi t) ^ (1 / 2 : ℝ)
        ≤ ENNReal.ofReal (Real.exp (-(t ^ 2) / 2)) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow
            ((measure_mono Ioi_subset_Ici_self).trans (gaussian_Ici_le ht')) (by norm_num)
      _ = ENNReal.ofReal (Real.exp (-(t ^ 2) / 4)) := sqrt_gaussian_bound t
  exact lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ioi key) hfin

/-- **Standard normal law satisfies the integrated square-root tail conditions.**
Both `∫_{(-∞,0)} (P(X ≤ t))^{1/2} dt` and `∫_{(0,∞)} (P(X > t))^{1/2} dt` are finite,
for `X` with the law `gaussianReal 0 1`. These are the hypotheses `hneg` and `hpos`
of Martin (2004), Theorem 2.4 (conditions (2.7) and (2.6)). -/
theorem gaussianReal_sqrt_tails :
    (∫⁻ t in Iio (0 : ℝ), (gaussianReal 0 1 (Iic t)) ^ (1 / 2 : ℝ)) < ∞ ∧
      (∫⁻ t in Ioi (0 : ℝ), (gaussianReal 0 1 (Ioi t)) ^ (1 / 2 : ℝ)) < ∞ :=
  ⟨gaussian_neg_sqrt_tail_lt_top, gaussian_pos_sqrt_tail_lt_top⟩

/-- **Standard normal law: mean 0 and variance 1.** The mean is `∫ t d(gaussianReal 0 1)`
and the variance is the integral of the squared deviation from the mean, in the same
form as in Martin (2004), Theorem 2.4. -/
theorem gaussianReal_mean_variance :
    ∫ t : ℝ, t ∂(gaussianReal 0 1) = 0 ∧
      ∫ t : ℝ, (t - ∫ s : ℝ, s ∂(gaussianReal 0 1)) ^ 2 ∂(gaussianReal 0 1) = 1 := by
  have hmean : ∫ t : ℝ, t ∂(gaussianReal 0 1) = 0 := integral_id_gaussianReal
  refine ⟨hmean, ?_⟩
  have hvar : ∫ ω : ℝ, (id ω - ∫ x : ℝ, id x ∂(gaussianReal 0 1)) ^ 2 ∂(gaussianReal 0 1) = 1 := by
    rw [← variance_eq_integral measurable_id.aemeasurable]
    simp [variance_id_gaussianReal]
  exact hvar

/-- The Exp(1) density at `x >= 0` is `ENNReal.ofReal (exp (-x))`. -/
private lemma gammaPDF_one_one_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    gammaPDF 1 1 x = ENNReal.ofReal (Real.exp (-x)) := by
  rw [gammaPDF_of_nonneg hx]
  congr 1
  simp [Real.Gamma_one]

/-- Exp(1) as a density: the integral of `f` against `expMeasure 1` is the integral over
`(0, infinity)` of `exp (-x) * f x`. -/
private lemma integral_expMeasure_one_eq (f : ℝ → ℝ) :
    ∫ x, f x ∂(expMeasure 1) = ∫ x in Ioi (0 : ℝ), Real.exp (-x) * f x := by
  have hmeas : Measurable (gammaPDF 1 1) :=
    ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal 1 1)
  have hfin : ∀ᵐ x ∂(volume : Measure ℝ), gammaPDF 1 1 x < ∞ :=
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hzero : ∀ x ∉ Ici (0 : ℝ), (gammaPDF 1 1 x).toReal • f x = 0 := by
    intro x hx
    have hx' : x < 0 := lt_of_not_ge (fun h => hx (Set.mem_Ici.2 h))
    rw [gammaPDF_of_neg hx', ENNReal.toReal_zero, zero_smul]
  calc ∫ x, f x ∂(expMeasure 1)
      = ∫ x, (gammaPDF 1 1 x).toReal • f x := by
        rw [expMeasure, gammaMeasure]
        exact integral_withDensity_eq_integral_toReal_smul hmeas hfin f
    _ = ∫ x in Ici (0 : ℝ), (gammaPDF 1 1 x).toReal • f x :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
    _ = ∫ x in Ioi (0 : ℝ), (gammaPDF 1 1 x).toReal • f x := integral_Ici_eq_integral_Ioi
    _ = ∫ x in Ioi (0 : ℝ), Real.exp (-x) * f x := by
        refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
        have hx0 : 0 ≤ x := (Set.mem_Ioi.1 hx).le
        show (gammaPDF 1 1 x).toReal • f x = Real.exp (-x) * f x
        rw [gammaPDF_one_one_of_nonneg hx0, ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul]

/-- The Gamma integral `∫_{(0,∞)} exp (-x) x = Gamma 2 = 1`. -/
private lemma integral_exp_mul_id : ∫ x in Ioi (0 : ℝ), Real.exp (-x) * x = 1 := by
  have h2 : Real.Gamma 2 = 1 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.Gamma_add_one (s := 1) one_ne_zero,
      Real.Gamma_one, one_mul]
  have h := Real.Gamma_eq_integral (s := 2) (by norm_num)
  rw [h2] at h
  simp only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one] at h
  exact h.symm

/-- The Gamma integral `∫_{(0,∞)} exp (-x) (x - 1)^2 = Gamma 3 - 2 Gamma 2 + Gamma 1 = 1`. -/
private lemma integral_exp_mul_sq_sub_one :
    ∫ x in Ioi (0 : ℝ), Real.exp (-x) * (x - 1) ^ 2 = 1 := by
  have h1 : Real.Gamma 1 = 1 := Real.Gamma_one
  have h2 : Real.Gamma 2 = 1 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.Gamma_add_one (s := 1) one_ne_zero,
      Real.Gamma_one, one_mul]
  have h3 : Real.Gamma 3 = 2 := by
    rw [show (3 : ℝ) = 2 + 1 by norm_num, Real.Gamma_add_one (s := 2) two_ne_zero, h2, mul_one]
  have hA : Integrable (fun x : ℝ => Real.exp (-x) * x ^ ((3 : ℝ) - 1))
      (volume.restrict (Ioi (0 : ℝ))) := Real.GammaIntegral_convergent (by norm_num)
  have hB : Integrable (fun x : ℝ => Real.exp (-x) * x ^ ((2 : ℝ) - 1))
      (volume.restrict (Ioi (0 : ℝ))) := Real.GammaIntegral_convergent (by norm_num)
  have hC : Integrable (fun x : ℝ => Real.exp (-x) * x ^ ((1 : ℝ) - 1))
      (volume.restrict (Ioi (0 : ℝ))) := Real.GammaIntegral_convergent (by norm_num)
  have hA' : ∫ x in Ioi (0 : ℝ), Real.exp (-x) * x ^ ((3 : ℝ) - 1) = 2 := by
    have h := Real.Gamma_eq_integral (s := 3) (by norm_num)
    rw [h3] at h
    exact h.symm
  have hB' : ∫ x in Ioi (0 : ℝ), Real.exp (-x) * x ^ ((2 : ℝ) - 1) = 1 := by
    have h := Real.Gamma_eq_integral (s := 2) (by norm_num)
    rw [h2] at h
    exact h.symm
  have hC' : ∫ x in Ioi (0 : ℝ), Real.exp (-x) * x ^ ((1 : ℝ) - 1) = 1 := by
    have h := Real.Gamma_eq_integral (s := 1) (by norm_num)
    rw [h1] at h
    exact h.symm
  have hpt : ∀ x : ℝ, Real.exp (-x) * (x - 1) ^ 2 =
      (Real.exp (-x) * x ^ ((3 : ℝ) - 1) - 2 * (Real.exp (-x) * x ^ ((2 : ℝ) - 1))) +
        Real.exp (-x) * x ^ ((1 : ℝ) - 1) := by
    intro x
    rw [show (3 : ℝ) - 1 = 2 by norm_num, show (2 : ℝ) - 1 = 1 by norm_num,
      show (1 : ℝ) - 1 = 0 by norm_num, Real.rpow_two, Real.rpow_one, Real.rpow_zero]
    ring
  have hAB : Integrable (fun x : ℝ => Real.exp (-x) * x ^ ((3 : ℝ) - 1) -
      2 * (Real.exp (-x) * x ^ ((2 : ℝ) - 1))) (volume.restrict (Ioi (0 : ℝ))) :=
    hA.sub (hB.const_mul 2)
  have e1 : ∫ x in Ioi (0 : ℝ), (Real.exp (-x) * x ^ ((3 : ℝ) - 1) -
      2 * (Real.exp (-x) * x ^ ((2 : ℝ) - 1))) + Real.exp (-x) * x ^ ((1 : ℝ) - 1) =
      (∫ x in Ioi (0 : ℝ), (Real.exp (-x) * x ^ ((3 : ℝ) - 1) -
        2 * (Real.exp (-x) * x ^ ((2 : ℝ) - 1)))) +
        ∫ x in Ioi (0 : ℝ), Real.exp (-x) * x ^ ((1 : ℝ) - 1) :=
    integral_add hAB hC
  have e2 : ∫ x in Ioi (0 : ℝ), (Real.exp (-x) * x ^ ((3 : ℝ) - 1) -
      2 * (Real.exp (-x) * x ^ ((2 : ℝ) - 1))) =
      (∫ x in Ioi (0 : ℝ), Real.exp (-x) * x ^ ((3 : ℝ) - 1)) -
        ∫ x in Ioi (0 : ℝ), 2 * (Real.exp (-x) * x ^ ((2 : ℝ) - 1)) :=
    integral_sub hA (hB.const_mul 2)
  have e3 : ∫ x in Ioi (0 : ℝ), 2 * (Real.exp (-x) * x ^ ((2 : ℝ) - 1)) =
      2 * ∫ x in Ioi (0 : ℝ), Real.exp (-x) * x ^ ((2 : ℝ) - 1) :=
    integral_const_mul (2 : ℝ) (fun x => Real.exp (-x) * x ^ ((2 : ℝ) - 1))
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x _ => hpt x), e1, e2, e3, hA', hB', hC']
  norm_num

/-- The Exp(1) lower tail vanishes below zero. -/
private lemma expMeasure_one_Iic_eq_zero {t : ℝ} (ht : t < 0) : expMeasure 1 (Iic t) = 0 := by
  have := isProbabilityMeasure_expMeasure one_pos
  have h := ofReal_cdf (expMeasure 1) t
  simp only [cdf_expMeasure_eq one_pos, not_le.2 ht, ↓reduceIte] at h
  rw [← h, ENNReal.ofReal_zero]

/-- Exp(1), lower integrated square-root tail (Martin condition (2.7)). -/
private lemma expMeasure_one_neg_sqrt_tail_lt_top :
    (∫⁻ t in Iio (0 : ℝ), (expMeasure 1 (Iic t)) ^ (1 / 2 : ℝ)) < ∞ := by
  have h0 : (∫⁻ t in Iio (0 : ℝ), (expMeasure 1 (Iic t)) ^ (1 / 2 : ℝ)) = 0 := by
    refine le_antisymm ?_ zero_le
    calc (∫⁻ t in Iio (0 : ℝ), (expMeasure 1 (Iic t)) ^ (1 / 2 : ℝ))
        ≤ ∫⁻ _ in Iio (0 : ℝ), (0 : ℝ≥0∞) :=
          setLIntegral_mono' measurableSet_Iio fun t ht => le_of_eq (by
            rw [expMeasure_one_Iic_eq_zero (Set.mem_Iio.1 ht),
              ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)])
      _ = 0 := by simp
  rw [h0]
  exact ENNReal.zero_lt_top

/-- Exp(1), upper integrated square-root tail (Martin condition (2.6)). -/
private lemma expMeasure_one_pos_sqrt_tail_lt_top :
    (∫⁻ t in Ioi (0 : ℝ), (expMeasure 1 (Ioi t)) ^ (1 / 2 : ℝ)) < ∞ := by
  have hI : Integrable (fun t : ℝ => Real.exp (-(1 / 2) * t)) (volume.restrict (Ioi (0 : ℝ))) :=
    exp_neg_integrableOn_Ioi 0 (by norm_num)
  have hfin : ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(1 / 2) * t)) < ∞ :=
    hI.lintegral_lt_top
  have key : ∀ t ∈ Ioi (0 : ℝ),
      expMeasure 1 (Ioi t) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (Real.exp (-(1 / 2) * t)) := by
    intro t ht
    have ht' : 0 ≤ t := (Set.mem_Ioi.1 ht).le
    have heq : expMeasure 1 (Ioi t) ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.exp (-(1 / 2) * t)) := by
      rw [expMeasure_one_Ioi ht', ENNReal.ofReal_rpow_of_nonneg (Real.exp_nonneg (-t))
        (by norm_num : (0 : ℝ) ≤ 1 / 2), ← Real.exp_mul,
        show -t * (1 / 2 : ℝ) = -(1 / 2) * t by ring]
    exact le_of_eq heq
  exact lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ioi key) hfin

/-- **Exp(1) satisfies the integrated square-root tail conditions.** Both
`∫_{(-∞,0)} (P(X ≤ t))^{1/2} dt` and `∫_{(0,∞)} (P(X > t))^{1/2} dt` are finite, for `X`
with the law `expMeasure 1`. These are the hypotheses `hneg` and `hpos` of Martin (2004),
Theorem 2.4 (conditions (2.7) and (2.6)). -/
theorem expMeasure_one_sqrt_tails :
    (∫⁻ t in Iio (0 : ℝ), (expMeasure 1 (Iic t)) ^ (1 / 2 : ℝ)) < ∞ ∧
      (∫⁻ t in Ioi (0 : ℝ), (expMeasure 1 (Ioi t)) ^ (1 / 2 : ℝ)) < ∞ :=
  ⟨expMeasure_one_neg_sqrt_tail_lt_top, expMeasure_one_pos_sqrt_tail_lt_top⟩

/-- **Exp(1) has mean 1 and variance 1.** The variance is the integral of the squared
deviation from the mean, in the same form as in Martin (2004), Theorem 2.4. -/
theorem expMeasure_one_mean_variance :
    ∫ t : ℝ, t ∂(expMeasure 1) = 1 ∧
      ∫ t : ℝ, (t - ∫ s : ℝ, s ∂(expMeasure 1)) ^ 2 ∂(expMeasure 1) = 1 := by
  have hmean : ∫ t : ℝ, t ∂(expMeasure 1) = 1 :=
    (integral_expMeasure_one_eq (fun t => t)).trans integral_exp_mul_id
  refine ⟨hmean, ?_⟩
  rw [hmean]
  exact (integral_expMeasure_one_eq (fun t => (t - 1) ^ 2)).trans integral_exp_mul_sq_sub_one

end LPPDifferentiability

end
