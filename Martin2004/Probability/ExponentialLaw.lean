/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Probability.CoordinateLaw
public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Exponential laws: the elementary facts used by the exponential shape

Martin (2004) uses the shape for exponential weights in the proof of Theorem 2.4. This file
collects the basic facts about the exponential law that this use needs.

Mathlib has the density and the cumulative distribution function of
`expMeasure r`. This file adds the following:

* the instances `SigmaFinite (expMeasure r)` and `IsProbabilityMeasure (expMeasure 1)`;
* scaling: `Exp(1) / r` has law `Exp(r)`;
* `Exp(r)` gives no mass to the negative half line;
* the mean `1 / r` and the second moment `2 / r ^ 2`, each with integrability;
* the three hypotheses of the shape theorem for `Exp(1)` (a first moment and both
  square-root tail integrals), in the `hneg`/`hpos` form used by the later files;
* almost sure nonnegativity of all site weights of the `Exp(1)` environment.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace LPPDifferentiability

/-! ## Instances -/

/-- Every exponential law `expMeasure r` is a density measure with respect to
Lebesgue measure, hence sigma-finite (needed to form finite products). -/
instance sigmaFinite_expMeasure (r : ℝ) : SigmaFinite (expMeasure r) := by
  have h : expMeasure r = volume.withDensity
      (fun t : ℝ => ENNReal.ofReal (exponentialPDFReal r t)) := rfl
  rw [h]
  infer_instance

/-- The rate-one exponential law is a probability measure (instance form of
Mathlib's `isProbabilityMeasure_expMeasure one_pos`). -/
instance isProbabilityMeasure_expMeasure_one : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure one_pos

/-! ## The cumulative distribution function and scaling -/

/-- The mass of a left half line under `Exp(r)`, read off the cumulative
distribution function. -/
private theorem expMeasure_Iic {r : ℝ} (hr : 0 < r) (t : ℝ) :
    expMeasure r (Iic t) = ENNReal.ofReal (if 0 ≤ t then 1 - Real.exp (-(r * t)) else 0) := by
  have := isProbabilityMeasure_expMeasure hr
  rw [← ofReal_cdf, cdf_expMeasure_eq hr]

/-- Dividing an Exp(1) variable by r > 0 gives an Exp(r) variable. -/
theorem expMeasure_one_map_div {r : ℝ} (hr : 0 < r) :
    (expMeasure 1).map (fun t : ℝ => t / r) = expMeasure r := by
  have hmeas : Measurable (fun t : ℝ => t / r) := measurable_id.div_const r
  have := isProbabilityMeasure_expMeasure hr
  refine Measure.ext_of_Iic _ _ fun s => ?_
  have hpre : (fun t : ℝ => t / r) ⁻¹' Iic s = Iic (r * s) := by
    ext t
    simp only [mem_preimage, mem_Iic]
    rw [div_le_iff₀ hr, mul_comm]
  have hnonneg : 0 ≤ r * s ↔ 0 ≤ s := by
    constructor
    · intro h
      exact nonneg_of_mul_nonneg_right h hr
    · intro h
      exact mul_nonneg hr.le h
  rw [Measure.map_apply hmeas measurableSet_Iic, hpre, expMeasure_Iic one_pos,
    expMeasure_Iic hr, one_mul]
  simp only [hnonneg]

/-- An exponential variable is almost surely nonnegative. -/
theorem expMeasure_Iio_zero (r : ℝ) : expMeasure r (Iio 0) = 0 := by
  have h : expMeasure r = volume.withDensity (exponentialPDF r) := rfl
  rw [h, withDensity_apply _ measurableSet_Iio]
  exact lintegral_exponentialPDF_of_nonpos le_rfl

/-! ## Moments -/

/-- Integrals against `Exp(r)` become integrals over the positive half line against the
density, for any real function. Integrability transfers in the same way. -/
private theorem integrable_expMeasure_iff {r : ℝ} (hr : 0 < r) (f : ℝ → ℝ) :
    Integrable f (expMeasure r) ↔
      IntegrableOn (fun t => r * Real.exp (-(r * t)) * f t) (Ioi 0) := by
  have h : expMeasure r = volume.withDensity (exponentialPDF r) := rfl
  have hmeas : Measurable (exponentialPDF r) :=
    (measurable_exponentialPDFReal r).ennreal_ofReal
  have hlt : ∀ᵐ t ∂(volume : Measure ℝ), exponentialPDF r t < ∞ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  rw [h, integrable_withDensity_iff_integrable_smul' hmeas hlt]
  have hfun : (fun t => (exponentialPDF r t).toReal • f t) =
      (Ici (0 : ℝ)).indicator (fun t => r * Real.exp (-(r * t)) * f t) := by
    funext t
    by_cases ht : 0 ≤ t
    · simp [exponentialPDF, exponentialPDFReal, gammaPDFReal, ht,
        ENNReal.toReal_ofReal (mul_nonneg hr.le (Real.exp_pos _).le)]
    · simp [exponentialPDF, exponentialPDFReal, gammaPDFReal, ht]
  rw [hfun, integrable_indicator_iff measurableSet_Ici, IntegrableOn,
    Measure.restrict_congr_set Ioi_ae_eq_Ici.symm]
  rfl

/-- The integral version of `integrable_expMeasure_iff`. -/
private theorem integral_expMeasure_eq {r : ℝ} (hr : 0 < r) (f : ℝ → ℝ) :
    ∫ t, f t ∂expMeasure r = ∫ t in Ioi 0, r * Real.exp (-(r * t)) * f t := by
  have h : expMeasure r = volume.withDensity (exponentialPDF r) := rfl
  have hmeas : Measurable (exponentialPDF r) :=
    (measurable_exponentialPDFReal r).ennreal_ofReal
  have hlt : ∀ᵐ t ∂(volume : Measure ℝ), exponentialPDF r t < ∞ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  rw [h, integral_withDensity_eq_integral_toReal_smul hmeas hlt]
  have hfun : (fun t => (exponentialPDF r t).toReal • f t) =
      (Ici (0 : ℝ)).indicator (fun t => r * Real.exp (-(r * t)) * f t) := by
    funext t
    by_cases ht : 0 ≤ t
    · simp [exponentialPDF, exponentialPDFReal, gammaPDFReal, ht,
        ENNReal.toReal_ofReal (mul_nonneg hr.le (Real.exp_pos _).le)]
    · simp [exponentialPDF, exponentialPDFReal, gammaPDFReal, ht]
  rw [hfun, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]

/-- The `n`-th moment of `Exp(r)`: integrable, with integral `n! / r ^ n`. -/
private theorem integrable_and_integral_pow_expMeasure {r : ℝ} (hr : 0 < r) (n : ℕ) :
    Integrable (fun t : ℝ => t ^ n) (expMeasure r) ∧
      ∫ t : ℝ, t ^ n ∂expMeasure r = (n.factorial : ℝ) / r ^ n := by
  have ha : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  -- the Gamma integral, with the power written as a natural number power
  have hgamma : ∫ t in Ioi (0 : ℝ), t ^ n * Real.exp (-(r * t)) =
      (n.factorial : ℝ) / r ^ (n + 1) := by
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi ha hr
    rw [add_sub_cancel_right] at h
    have hcongr : ∫ t in Ioi (0 : ℝ), t ^ n * Real.exp (-(r * t)) =
        ∫ t in Ioi (0 : ℝ), t ^ (n : ℝ) * Real.exp (-(r * t)) :=
      setIntegral_congr_fun measurableSet_Ioi fun t _ => by rw [Real.rpow_natCast]
    rw [hcongr, h, Real.Gamma_nat_eq_factorial]
    have hpow : (1 / r) ^ ((n : ℝ) + 1) = 1 / r ^ (n + 1) := by
      rw [show ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
        one_div_pow]
    rw [hpow]
    ring
  have hint : IntegrableOn (fun t : ℝ => t ^ n * Real.exp (-(r * t))) (Ioi 0) := by
    refine Integrable.of_integral_ne_zero ?_
    rw [hgamma]
    positivity
  have hrewrite : (fun t : ℝ => r * Real.exp (-(r * t)) * t ^ n) =
      fun t => r * (t ^ n * Real.exp (-(r * t))) := by
    funext t
    ring
  refine ⟨(integrable_expMeasure_iff hr _).2 ?_, ?_⟩
  · rw [hrewrite]
    exact hint.const_mul r
  · rw [integral_expMeasure_eq hr, hrewrite, integral_const_mul, hgamma]
    field_simp
    ring

/-- Exp(r) has mean 1/r. -/
theorem integrable_and_integral_id_expMeasure {r : ℝ} (hr : 0 < r) :
    Integrable (fun t : ℝ => t) (expMeasure r) ∧ ∫ t : ℝ, t ∂expMeasure r = 1 / r := by
  simpa using integrable_and_integral_pow_expMeasure hr 1

/-- Exp(r) has second moment 2/r^2. -/
theorem integrable_and_integral_sq_expMeasure {r : ℝ} (hr : 0 < r) :
    Integrable (fun t : ℝ => t ^ 2) (expMeasure r) ∧
      ∫ t : ℝ, t ^ 2 ∂expMeasure r = 2 / r ^ 2 := by
  simpa [Nat.factorial] using integrable_and_integral_pow_expMeasure hr 2

/-! ## Martin's hypotheses for `Exp(1)` -/

/-- The mass of a right half line under `Exp(1)` at a nonnegative point. -/
theorem expMeasure_one_Ioi {t : ℝ} (ht : 0 ≤ t) :
    expMeasure 1 (Ioi t) = ENNReal.ofReal (Real.exp (-t)) := by
  have hcompl : Ioi t = (Iic t)ᶜ := compl_Iic.symm
  rw [hcompl, prob_compl_eq_one_sub measurableSet_Iic, expMeasure_Iic one_pos]
  simp only [ht, ↓reduceIte]
  have hreal : (1 : ℝ) - (1 - Real.exp (-(1 * t))) = Real.exp (-t) := by
    rw [one_mul]
    ring
  rw [← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub _ (sub_nonneg.2 (Real.exp_le_one_iff.2 (by linarith))), hreal]

/-- `Exp(1)` has a first moment and both square-root tail integrals finite, so the i.i.d. shape
theorem applies to it. -/
theorem expMeasure_one_martin_hypotheses :
    Integrable (fun t : ℝ => t) (expMeasure 1) ∧
    (∫⁻ t in Iio (0 : ℝ), (expMeasure 1 (Iic t)) ^ (1 / 2 : ℝ)) < ∞ ∧
    (∫⁻ t in Ioi (0 : ℝ), (expMeasure 1 (Ioi t)) ^ (1 / 2 : ℝ)) < ∞ := by
  refine ⟨(integrable_and_integral_id_expMeasure one_pos).1, ?_, ?_⟩
  · -- negative tail: the mass of `(-∞, t]` is zero for `t < 0`
    have hzero : ∀ t ∈ Iio (0 : ℝ), (expMeasure 1 (Iic t)) ^ (1 / 2 : ℝ) = 0 := by
      intro t ht
      have hsub : Iic t ⊆ Iio 0 := Iic_subset_Iio.2 ht
      rw [measure_mono_null hsub (expMeasure_Iio_zero 1)]
      exact ENNReal.zero_rpow_of_pos (by norm_num)
    rw [setLIntegral_congr_fun measurableSet_Iio hzero, lintegral_zero]
    exact ENNReal.zero_lt_top
  · -- positive tail: the integrand is `exp (-t / 2)`
    have hsqrt : ∀ t ∈ Ioi (0 : ℝ), (expMeasure 1 (Ioi t)) ^ (1 / 2 : ℝ) =
        ENNReal.ofReal (Real.exp ((-1 / 2) * t)) := by
      intro t ht
      rw [expMeasure_one_Ioi (le_of_lt ht),
        ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by norm_num),
        ← Real.exp_mul]
      congr 2
      ring
    rw [setLIntegral_congr_fun measurableSet_Ioi hsqrt]
    exact (integrableOn_exp_mul_Ioi (by norm_num : (-1 / 2 : ℝ) < 0) 0).lintegral_lt_top

/-! ## Nonnegativity of the environment -/

/-- Almost surely every site weight of the `Exp(1)` environment is nonnegative. -/
theorem ae_nonneg_environmentLaw_expMeasure_one :
    ∀ᵐ ω ∂environmentLaw (expMeasure 1), ∀ z, 0 ≤ ω z := by
  rw [ae_all_iff]
  intro z
  have hmap := environmentLaw_map_eval (expMeasure 1) z
  have hnull : environmentLaw (expMeasure 1) {ω | ω z < 0} = 0 := by
    have h := Measure.map_apply (μ := environmentLaw (expMeasure 1))
      (measurable_environment_eval z) (measurableSet_Iio (a := (0 : ℝ)))
    rw [hmap, expMeasure_Iio_zero] at h
    exact h.symm
  rw [ae_iff]
  simpa using hnull

end LPPDifferentiability
