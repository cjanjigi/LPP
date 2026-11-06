/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Probability.FiniteEnvironmentDensity
public import Differentiability.Probability.MaximumMixtureLaw
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Measure.WithDensity
import Differentiability.Probability.MaximumLawDensity

/-!
# The density for a finite regional maximum resampling

For a finite set of sites, this file specializes the one-site
maximum-resampling density to its actual affine factor and obtains the density
of the corresponding changed infinite product on the original environment.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace LPPDifferentiability

/-- The actual affine factor from the maximum-resampling kernel is measurable. -/
theorem measurable_maximum_regional_density (μ : Measure ℝ) (δ : ℝ) :
    Measurable (fun t : ℝ =>
      1 - δ + δ * (μ.real (Iic t) + μ.real (Iio t))) := by
  exact measurable_const.add
    (measurable_const.mul (measurable_maximum_density μ))

/-- The actual affine factor lies between zero and two for `δ ∈ [0,1]`. -/
theorem maximum_regional_density_mem_Icc (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {δ : ℝ} (hδ : δ ∈ Icc (0 : ℝ) 1) (t : ℝ) :
    1 - δ + δ * (μ.real (Iic t) + μ.real (Iio t)) ∈ Icc (0 : ℝ) 2 := by
  have hmax := maximum_density_mem_Icc μ t
  constructor
  · exact add_nonneg (sub_nonneg.mpr hδ.2) (mul_nonneg hδ.1 hmax.1)
  · have hδmax : δ * (μ.real (Iic t) + μ.real (Iio t)) ≤ δ * 2 :=
      mul_le_mul_of_nonneg_left hmax.2 hδ.1
    nlinarith only [hδ.2, hδmax]

/-- The actual regional affine factor is integrable under the original marginal. -/
theorem integrable_maximum_regional_density (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (δ : ℝ) :
    Integrable (fun t : ℝ =>
      1 - δ + δ * (μ.real (Iic t) + μ.real (Iio t))) μ :=
  integrable_maximum_mixture_density μ δ

/-- The actual regional affine factor has mean one. -/
theorem integral_maximum_regional_density (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (δ : ℝ) :
    (∫ t : ℝ, 1 - δ + δ * (μ.real (Iic t) + μ.real (Iio t)) ∂μ) = 1 := by
  have hbase : Integrable (fun t : ℝ => μ.real (Iic t) + μ.real (Iio t)) μ :=
    integrable_maximum_density μ
  rw [integral_add (integrable_const _) (hbase.const_mul δ)]
  simp only [integral_const, probReal_univ, one_smul, integral_const_mul,
    integral_maximum_density μ]
  ring

/-- The product of changed marginals has its actual density on the original
infinite iid environment. -/
theorem infinitePi_maximum_regional_withDensity (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {δ : ℝ} (hδ : δ ∈ Icc (0 : ℝ) 1)
    (R : Finset Lattice) :
    Measure.infinitePi (fun v : Lattice => if v ∈ R then
      μ.withDensity (fun t => ENNReal.ofReal
        (1 - δ + δ * (μ.real (Iic t) + μ.real (Iio t)))) else μ) =
      (environmentLaw μ).withDensity (fun ω : Environment =>
        ∏ v ∈ R, ENNReal.ofReal
          (1 - δ + δ * (μ.real (Iic (ω v)) + μ.real (Iio (ω v))))) := by
  let f : ℝ → ℝ := fun t => 1 - δ + δ * (μ.real (Iic t) + μ.real (Iio t))
  have hf : Measurable f := measurable_maximum_regional_density μ δ
  have h0 : ∀ t, 0 ≤ f t := fun t => (maximum_regional_density_mem_Icc μ hδ t).1
  have h2 : ∀ t, f t ≤ 2 := fun t => (maximum_regional_density_mem_Icc μ hδ t).2
  have hmean : ∫ t, f t ∂μ = 1 := integral_maximum_regional_density μ δ
  simpa only [f] using infinitePi_finite_withDensity μ R f hf h0 h2 hmean

/-- The actual finite product of regional factors is integrable on the original
infinite environment space. -/
theorem integrable_maximum_regional_product_density (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {δ : ℝ} (hδ : δ ∈ Icc (0 : ℝ) 1)
    (R : Finset Lattice) :
    Integrable (fun ω : Environment =>
      ∏ v ∈ R, (1 - δ + δ * (μ.real (Iic (ω v)) + μ.real (Iio (ω v)))))
      (environmentLaw μ) := by
  let f : ℝ → ℝ := fun t => 1 - δ + δ * (μ.real (Iic t) + μ.real (Iio t))
  have hf : Measurable f := measurable_maximum_regional_density μ δ
  have h0 : ∀ t, 0 ≤ f t := fun t => (maximum_regional_density_mem_Icc μ hδ t).1
  have h2 : ∀ t, f t ≤ 2 := fun t => (maximum_regional_density_mem_Icc μ hδ t).2
  simpa only [f] using integrable_prod_environment_factors μ R f hf h0 h2

/-- The actual finite regional product density has mean one. -/
theorem integral_maximum_regional_product_density (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {δ : ℝ} (R : Finset Lattice) :
    (∫ ω : Environment,
      ∏ v ∈ R, (1 - δ + δ * (μ.real (Iic (ω v)) + μ.real (Iio (ω v))))
        ∂environmentLaw μ) = 1 := by
  let f : ℝ → ℝ := fun t => 1 - δ + δ * (μ.real (Iic t) + μ.real (Iio t))
  have hf : Measurable f := measurable_maximum_regional_density μ δ
  have hmean : ∫ t, f t ∂μ = 1 := integral_maximum_regional_density μ δ
  simpa only [f] using integral_prod_environment_factors_eq_one μ R f hf hmean

/-- The square of the actual regional product density is integrable. -/
theorem integrable_sq_maximum_regional_product_density (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {δ : ℝ} (hδ : δ ∈ Icc (0 : ℝ) 1)
    (R : Finset Lattice) :
    Integrable (fun ω : Environment =>
      (∏ v ∈ R, (1 - δ + δ * (μ.real (Iic (ω v)) + μ.real (Iio (ω v))))) ^ 2)
      (environmentLaw μ) := by
  let f : ℝ → ℝ := fun t => 1 - δ + δ * (μ.real (Iic t) + μ.real (Iio t))
  have hf : Measurable f := measurable_maximum_regional_density μ δ
  have h0 : ∀ t, 0 ≤ f t := fun t => (maximum_regional_density_mem_Icc μ hδ t).1
  have h2 : ∀ t, f t ≤ 2 := fun t => (maximum_regional_density_mem_Icc μ hδ t).2
  simpa only [f] using integrable_sq_prod_environment_factors μ R f hf h0 h2

/-- The square moment of the actual regional product density factors exactly. -/
theorem integral_sq_maximum_regional_product_density (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {δ : ℝ} (R : Finset Lattice) :
    (∫ ω : Environment,
      (∏ v ∈ R, (1 - δ + δ * (μ.real (Iic (ω v)) + μ.real (Iio (ω v))))) ^ 2
        ∂environmentLaw μ) =
      (∫ t : ℝ,
        (1 - δ + δ * (μ.real (Iic t) + μ.real (Iio t))) ^ 2 ∂μ) ^ R.card := by
  let f : ℝ → ℝ := fun t => 1 - δ + δ * (μ.real (Iic t) + μ.real (Iio t))
  have hf : Measurable f := measurable_maximum_regional_density μ δ
  simpa only [f] using integral_sq_prod_environment_factors μ R f hf

/-- The actual regional product density has the exponential square-moment bound
`exp (3 δ² |R|)`. -/
theorem integral_sq_maximum_regional_product_density_le (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {δ : ℝ} (hδ : δ ∈ Icc (0 : ℝ) 1)
    (R : Finset Lattice) :
    (∫ ω : Environment,
      (∏ v ∈ R, (1 - δ + δ * (μ.real (Iic (ω v)) + μ.real (Iio (ω v))))) ^ 2
        ∂environmentLaw μ) ≤ Real.exp (3 * δ ^ 2 * R.card) := by
  let f : ℝ → ℝ := fun t => 1 - δ + δ * (μ.real (Iic t) + μ.real (Iio t))
  have hf : Measurable f := measurable_maximum_regional_density μ δ
  have hcost := integral_maximum_mixture_density_sq_le μ hδ
  have h := integral_sq_prod_environment_factors_le_exp μ R f hf δ hcost
  simpa only [f] using h

/-- The actual regional product law is absolutely continuous with respect to the
original infinite environment law, including when a factor vanishes. -/
theorem infinitePi_maximum_regional_absolutelyContinuous (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {δ : ℝ} (hδ : δ ∈ Icc (0 : ℝ) 1)
    (R : Finset Lattice) :
    Measure.infinitePi (fun v : Lattice => if v ∈ R then
      μ.withDensity (fun t => ENNReal.ofReal
        (1 - δ + δ * (μ.real (Iic t) + μ.real (Iio t)))) else μ) ≪ environmentLaw μ := by
  let f : ℝ → ℝ := fun t => 1 - δ + δ * (μ.real (Iic t) + μ.real (Iio t))
  have hf : Measurable f := measurable_maximum_regional_density μ δ
  have h0 : ∀ t, 0 ≤ f t := fun t => (maximum_regional_density_mem_Icc μ hδ t).1
  have h2 : ∀ t, f t ≤ 2 := fun t => (maximum_regional_density_mem_Icc μ hδ t).2
  have hmean : ∫ t, f t ∂μ = 1 := integral_maximum_regional_density μ δ
  simpa only [f] using
    infinitePi_finite_withDensity_absolutelyContinuous μ R f hf h0 h2 hmean

end LPPDifferentiability
