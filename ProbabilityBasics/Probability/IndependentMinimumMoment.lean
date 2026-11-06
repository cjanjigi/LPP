/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Distributions.Bernoulli

/-!
# Second moments of independent minima

For independent nonnegative integrable real random variables, the square of
their minimum is bounded by their product. Independence and the first moments
make that product integrable, so the minimum has a finite second moment.
-/

public section

open MeasureTheory ProbabilityTheory

namespace LPPDifferentiability

private theorem min_sq_le_mul_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    min a b ^ 2 ≤ a * b := by
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab]
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hab)]
  · rw [min_eq_right hba]
    nlinarith [mul_nonneg hb (sub_nonneg.mpr hba)]

private theorem min_sq_nonneg_ae {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {U V : Ω → ℝ} :
    0 ≤ᵐ[μ] (fun ω => min (U ω) (V ω) ^ 2) := by
  filter_upwards [] with ω
  exact sq_nonneg (min (U ω) (V ω))

private theorem min_sq_le_mul_ae {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {U V : Ω → ℝ} (hU_nonneg : 0 ≤ᵐ[μ] U) (hV_nonneg : 0 ≤ᵐ[μ] V) :
    (fun ω => min (U ω) (V ω) ^ 2) ≤ᵐ[μ] U * V := by
  filter_upwards [hU_nonneg, hV_nonneg] with ω hUω hVω
  exact min_sq_le_mul_of_nonneg hUω hVω

/-- The square of the minimum of two independent nonnegative integrable real
random variables is integrable. No second moment or product integrability is
assumed. -/
theorem integrable_min_sq_of_indep {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {U V : Ω → ℝ} (hUV : U ⟂ᵢ[μ] V) (hU : Integrable U μ) (hV : Integrable V μ)
    (hU_nonneg : 0 ≤ᵐ[μ] U) (hV_nonneg : 0 ≤ᵐ[μ] V) :
    Integrable (fun ω => min (U ω) (V ω) ^ 2) μ := by
  have hUV_int : Integrable (U * V) μ := hUV.integrable_mul hU hV
  have hmin_aemeas : AEMeasurable (fun ω => min (U ω) (V ω)) μ :=
    hU.aemeasurable.min hV.aemeasurable
  have hmin_sq_aemeas : AEMeasurable (fun ω => min (U ω) (V ω) ^ 2) μ :=
    hmin_aemeas.pow_const 2
  exact hUV_int.mono_nonneg hmin_sq_aemeas.aestronglyMeasurable
    min_sq_nonneg_ae (min_sq_le_mul_ae hU_nonneg hV_nonneg)

/-- The expected square of the minimum is at most the product of the first
moments for independent nonnegative integrable real random variables. -/
theorem integral_min_sq_le_mul_integral_of_indep {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {U V : Ω → ℝ} (hUV : U ⟂ᵢ[μ] V)
    (hU : Integrable U μ) (hV : Integrable V μ)
    (hU_nonneg : 0 ≤ᵐ[μ] U) (hV_nonneg : 0 ≤ᵐ[μ] V) :
    (∫ ω, min (U ω) (V ω) ^ 2 ∂μ) ≤
      (∫ ω, U ω ∂μ) * (∫ ω, V ω ∂μ) := by
  have hUV_int : Integrable (U * V) μ := hUV.integrable_mul hU hV
  have hmin_sq_int := integrable_min_sq_of_indep hUV hU hV hU_nonneg hV_nonneg
  calc
    (∫ ω, min (U ω) (V ω) ^ 2 ∂μ) ≤ ∫ ω, (U * V) ω ∂μ :=
      integral_mono_ae hmin_sq_int hUV_int (min_sq_le_mul_ae hU_nonneg hV_nonneg)
    _ = (∫ ω, U ω ∂μ) * (∫ ω, V ω ∂μ) := by
      simpa only [Pi.mul_apply] using
        hUV.integral_mul_eq_mul_integral hU.aestronglyMeasurable hV.aestronglyMeasurable

private theorem constant_zero_three_test {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] :
    Integrable (fun _ : Ω => min (0 : ℝ) 3 ^ 2) μ ∧
      (∫ _, min (0 : ℝ) 3 ^ 2 ∂μ) ≤
        (∫ _, (0 : ℝ) ∂μ) * (∫ _, (3 : ℝ) ∂μ) := by
  let U : Ω → ℝ := fun _ => 0
  let V : Ω → ℝ := fun _ => 3
  have hUV : U ⟂ᵢ[μ] V := by
    simpa only [U, V] using indepFun_const_left (μ := μ) (0 : ℝ) V
  have hU : Integrable U μ := integrable_const _
  have hV : Integrable V μ := integrable_const _
  have hU_nonneg : 0 ≤ᵐ[μ] U := by
    filter_upwards [] with ω
    simp [U]
  have hV_nonneg : 0 ≤ᵐ[μ] V := by
    filter_upwards [] with ω
    norm_num [V]
  constructor
  · exact integrable_min_sq_of_indep hUV hU hV hU_nonneg hV_nonneg
  · exact integral_min_sq_le_mul_integral_of_indep hUV hU hV hU_nonneg hV_nonneg

private noncomputable def first_two_point_law : Measure Bool :=
  bernoulliMeasure false true ⟨(1 / 3 : ℝ), by norm_num⟩

private noncomputable def second_two_point_law : Measure Bool :=
  bernoulliMeasure false true ⟨(1 / 4 : ℝ), by norm_num⟩

private instance first_two_point_law_isProbabilityMeasure :
    IsProbabilityMeasure first_two_point_law := by
  dsimp [first_two_point_law]
  infer_instance

private instance second_two_point_law_isProbabilityMeasure :
    IsProbabilityMeasure second_two_point_law := by
  dsimp [second_two_point_law]
  infer_instance

private def first_two_point_value (b : Bool) : ℝ := if b then 1 else 0

private def second_two_point_value (b : Bool) : ℝ := if b then 4 else 2

private theorem unequal_two_point_product_test :
    Integrable
        (fun ω : Bool × Bool =>
          min (first_two_point_value ω.1) (second_two_point_value ω.2) ^ 2)
        (first_two_point_law.prod second_two_point_law) ∧
      (∫ ω : Bool × Bool,
          min (first_two_point_value ω.1) (second_two_point_value ω.2) ^ 2
          ∂ first_two_point_law.prod second_two_point_law) ≤
        (∫ ω : Bool × Bool, first_two_point_value ω.1
          ∂ first_two_point_law.prod second_two_point_law) *
        (∫ ω : Bool × Bool, second_two_point_value ω.2
          ∂ first_two_point_law.prod second_two_point_law) := by
  have hX : Integrable first_two_point_value first_two_point_law :=
    integrable_bernoulliMeasure false true
      ⟨(1 / 3 : ℝ), by norm_num⟩ first_two_point_value
  have hY : Integrable second_two_point_value second_two_point_law :=
    integrable_bernoulliMeasure false true
      ⟨(1 / 4 : ℝ), by norm_num⟩ second_two_point_value
  have hU :
      Integrable (fun ω : Bool × Bool => first_two_point_value ω.1)
        (first_two_point_law.prod second_two_point_law) :=
    hX.comp_fst second_two_point_law
  have hV :
      Integrable (fun ω : Bool × Bool => second_two_point_value ω.2)
        (first_two_point_law.prod second_two_point_law) :=
    hY.comp_snd first_two_point_law
  have hUV :
      (fun ω : Bool × Bool => first_two_point_value ω.1)
        ⟂ᵢ[first_two_point_law.prod second_two_point_law]
        (fun ω : Bool × Bool => second_two_point_value ω.2) := by
    exact indepFun_prod (μ := first_two_point_law) (ν := second_two_point_law)
      (X := first_two_point_value) (Y := second_two_point_value) (by fun_prop) (by fun_prop)
  have hU_nonneg :
      0 ≤ᵐ[first_two_point_law.prod second_two_point_law]
        (fun ω : Bool × Bool => first_two_point_value ω.1) := by
    filter_upwards [] with ω
    cases ω.1 <;> simp [first_two_point_value]
  have hV_nonneg :
      0 ≤ᵐ[first_two_point_law.prod second_two_point_law]
        (fun ω : Bool × Bool => second_two_point_value ω.2) := by
    filter_upwards [] with ω
    cases ω.2 <;> norm_num [second_two_point_value]
  constructor
  · exact integrable_min_sq_of_indep hUV hU hV hU_nonneg hV_nonneg
  · exact integral_min_sq_le_mul_integral_of_indep hUV hU hV hU_nonneg hV_nonneg

end LPPDifferentiability
