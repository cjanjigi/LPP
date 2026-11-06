/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# A bounded fiber Hoeffding step

This file proves one step of the Hoeffding argument for a bounded function of two variables.
Integrating out one independent coordinate gives a partial integral. Pointwise oscillation
bounds center every fiber in the same fixed interval. Hoeffding's bound and Fubini's theorem
then give one step of the iteration for the product moment generating function.
-/

public section

open MeasureTheory ProbabilityTheory

namespace LPPDifferentiability

variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

/-- Every section of a measurable bounded function is integrable. -/
theorem integrable_fiber_of_abs_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Ω × A → ℝ) (M : ℝ) (hF : Measurable F)
    (hbound : ∀ z, |F z| ≤ M) (a : A) :
    Integrable (fun x => F (x, a)) μ := by
  refine (integrable_const M).mono' (hF.comp
    (measurable_id.prodMk measurable_const)).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall (fun x => (Real.norm_eq_abs _).symm ▸ hbound (x, a))

/-- A bounded measurable function is integrable under every product of probability measures. -/
theorem integrable_prod_of_abs_le (μ : Measure Ω) (ν : Measure A)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : Ω × A → ℝ) (M : ℝ) (hF : Measurable F)
    (hbound : ∀ z, |F z| ≤ M) : Integrable F (μ.prod ν) := by
  refine (integrable_const M).mono' hF.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall (fun z => (Real.norm_eq_abs _).symm ▸ hbound z)

/-- The partial integral over the first coordinate is measurable in the parameter. -/
theorem measurable_integral_fiber (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Ω × A → ℝ) (hF : Measurable F) :
    Measurable (fun a => ∫ x, F (x, a) ∂μ) :=
  hF.stronglyMeasurable.integral_prod_left'.measurable

omit [MeasurableSpace A] in
/-- The partial integral retains the global absolute bound, at every parameter. -/
theorem abs_integral_fiber_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Ω × A → ℝ) (M : ℝ) (hbound : ∀ z, |F z| ≤ M) (a : A) :
    |∫ x, F (x, a) ∂μ| ≤ M := by
  have h := norm_integral_le_of_norm_le_const
    (μ := μ) (Filter.Eventually.of_forall (fun x =>
      (Real.norm_eq_abs _).symm ▸ hbound (x, a)))
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using h

/-- The partial integral is integrable in the parameter. -/
theorem integrable_integral_fiber (μ : Measure Ω) (ν : Measure A)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : Ω × A → ℝ) (M : ℝ) (hF : Measurable F)
    (hbound : ∀ z, |F z| ≤ M) :
    Integrable (fun a => ∫ x, F (x, a) ∂μ) ν :=
  (integrable_prod_of_abs_le μ ν F M hF hbound).integral_prod_right

/-- Fubini identifies the partial mean with the full product mean. -/
theorem integral_integral_fiber (μ : Measure Ω) (ν : Measure A)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : Ω × A → ℝ) (M : ℝ) (hF : Measurable F)
    (hbound : ∀ z, |F z| ≤ M) :
    (∫ a, ∫ x, F (x, a) ∂μ ∂ν) = ∫ z, F z ∂μ.prod ν :=
  (integral_prod_symm F (integrable_prod_of_abs_le μ ν F M hF hbound)).symm

/-- A centered fiber is integrable for every parameter. -/
theorem integrable_centered_fiber (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Ω × A → ℝ) (M : ℝ) (hF : Measurable F)
    (hbound : ∀ z, |F z| ≤ M) (a : A) :
    Integrable (fun x => F (x, a) - ∫ y, F (y, a) ∂μ) μ :=
  (integrable_fiber_of_abs_le μ F M hF hbound a).sub (integrable_const _)

/-- Centering each fiber by its mean gives mean zero, for every parameter. -/
theorem integral_centered_fiber (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Ω × A → ℝ) (M : ℝ) (hF : Measurable F)
    (hbound : ∀ z, |F z| ≤ M) (a : A) :
    (∫ x, (F (x, a) - ∫ y, F (y, a) ∂μ) ∂μ) = 0 := by
  rw [integral_sub (integrable_fiber_of_abs_le μ F M hF hbound a)
    (integrable_const _)]
  simp only [integral_const, probReal_univ, one_smul, sub_self]

/-- Integrating the oscillation inequality bounds every centered fiber value. -/
theorem abs_centered_fiber_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Ω × A → ℝ) (M b : ℝ) (hF : Measurable F)
    (hbound : ∀ z, |F z| ≤ M)
    (hosc : ∀ a x y, |F (x, a) - F (y, a)| ≤ b) (a : A) (x : Ω) :
    |F (x, a) - ∫ y, F (y, a) ∂μ| ≤ b := by
  have heq : F (x, a) - ∫ y, F (y, a) ∂μ =
      ∫ y, (F (x, a) - F (y, a)) ∂μ := by
    rw [integral_sub (integrable_const _)
      (integrable_fiber_of_abs_le μ F M hF hbound a)]
    simp only [integral_const, probReal_univ, one_smul]
  rw [heq]
  have h := norm_integral_le_of_norm_le_const (μ := μ)
    (Filter.Eventually.of_forall (fun y =>
      (Real.norm_eq_abs _).symm ▸ hosc a x y))
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using h

/-- Hoeffding's bound for a centered variable with values in a fixed interval applies to each
fiber, for every real `t`. -/
theorem integral_exp_centered_fiber_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Ω × A → ℝ) (M b : ℝ) (hb : 0 ≤ b) (hF : Measurable F)
    (hbound : ∀ z, |F z| ≤ M)
    (hosc : ∀ a x y, |F (x, a) - F (y, a)| ≤ b) (a : A) (t : ℝ) :
    (∫ x, Real.exp (t * (F (x, a) - ∫ y, F (y, a) ∂μ)) ∂μ) ≤
      Real.exp (b ^ 2 * t ^ 2 / 2) := by
  have hm : Measurable (fun x => F (x, a) - ∫ y, F (y, a) ∂μ) :=
    (hF.comp (measurable_id.prodMk measurable_const)).sub_const _
  have hinterval : ∀ᵐ x ∂μ,
      (F (x, a) - ∫ y, F (y, a) ∂μ) ∈ Set.Icc (-b) b :=
    Filter.Eventually.of_forall (fun x =>
      abs_le.mp (abs_centered_fiber_le μ F M b hF hbound hosc a x))
  have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hm.aemeasurable
    hinterval (integral_centered_fiber μ F M hF hbound a)
  have hnorm : ‖b - -b‖ = 2 * b := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith only [hb])]
    ring
  have hcoef : (((‖b - -b‖₊ / 2) ^ 2 : NNReal) : ℝ) = b ^ 2 := by
    push_cast
    rw [hnorm]
    ring
  simpa only [mgf, hcoef] using h.mgf_le t

/-- A bounded oscillation gives integrability of the exponential of each centered fiber, for
every real `t`. -/
theorem integrable_exp_centered_fiber (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Ω × A → ℝ) (M b : ℝ) (hF : Measurable F)
    (hbound : ∀ z, |F z| ≤ M)
    (hosc : ∀ a x y, |F (x, a) - F (y, a)| ≤ b) (a : A) (t : ℝ) :
    Integrable (fun x => Real.exp (t * (F (x, a) - ∫ y, F (y, a) ∂μ))) μ := by
  apply integrable_exp_mul_of_mem_Icc
    ((hF.comp (measurable_id.prodMk measurable_const)).sub_const _).aemeasurable
  exact Filter.Eventually.of_forall (fun x =>
    abs_le.mp (abs_centered_fiber_le μ F M b hF hbound hosc a x))

/-- Bounded real functions have integrable centered exponentials at every real t. -/
theorem integrable_exp_mul_sub_const_of_abs_le (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : Ω → ℝ) (M : ℝ) (hf : Measurable f) (hbound : ∀ x, |f x| ≤ M)
    (c t : ℝ) : Integrable (fun x => Real.exp (t * (f x - c))) μ := by
  apply integrable_exp_mul_of_mem_Icc (a := -M - c) (b := M - c)
    (hf.sub_const c).aemeasurable
  exact Filter.Eventually.of_forall (fun x =>
    ⟨sub_le_sub_right (abs_le.mp (hbound x)).1 c,
      sub_le_sub_right (abs_le.mp (hbound x)).2 c⟩)

/-- Every section exponential centered at any real constant is integrable. -/
theorem integrable_exp_fiber_sub_const (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Ω × A → ℝ) (M : ℝ) (hF : Measurable F)
    (hbound : ∀ z, |F z| ≤ M) (a : A) (c t : ℝ) :
    Integrable (fun x => Real.exp (t * (F (x, a) - c))) μ :=
  integrable_exp_mul_sub_const_of_abs_le μ (fun x => F (x, a)) M
    (hF.comp (measurable_id.prodMk measurable_const)) (fun x => hbound (x, a)) c t

/-- The product exponential centered at any real constant is integrable. -/
theorem integrable_exp_prod_sub_const (μ : Measure Ω) (ν : Measure A)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : Ω × A → ℝ) (M : ℝ) (hF : Measurable F)
    (hbound : ∀ z, |F z| ≤ M) (c t : ℝ) :
    Integrable (fun z => Real.exp (t * (F z - c))) (μ.prod ν) :=
  integrable_exp_mul_sub_const_of_abs_le (μ.prod ν) F M hF hbound c t

/-- The average exponential centered at any real constant is integrable. -/
theorem integrable_exp_integral_fiber_sub_const (μ : Measure Ω) (ν : Measure A)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : Ω × A → ℝ) (M : ℝ) (hF : Measurable F)
    (hbound : ∀ z, |F z| ≤ M) (c t : ℝ) :
    Integrable (fun a => Real.exp (t * ((∫ x, F (x, a) ∂μ) - c))) ν :=
  integrable_exp_mul_sub_const_of_abs_le ν (fun a => ∫ x, F (x, a) ∂μ) M
    (measurable_integral_fiber μ F hF) (abs_integral_fiber_le μ F M hbound) c t

/-- The jointly centered function is measurable and integrable on the product. -/
theorem integrable_centered_fiber_prod (μ : Measure Ω) (ν : Measure A)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : Ω × A → ℝ) (M b : ℝ) (hF : Measurable F)
    (hbound : ∀ z, |F z| ≤ M)
    (hosc : ∀ a x y, |F (x, a) - F (y, a)| ≤ b) :
    Integrable (fun z => F z - ∫ y, F (y, z.2) ∂μ) (μ.prod ν) := by
  refine (integrable_const b).mono'
    (hF.sub ((measurable_integral_fiber μ F hF).comp measurable_snd)).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall (fun z =>
    (Real.norm_eq_abs _).symm ▸ abs_centered_fiber_le μ F M b hF hbound hosc z.2 z.1)

/-- The exponential of the fiber-centered function is integrable on the product. -/
theorem integrable_exp_centered_fiber_prod (μ : Measure Ω) (ν : Measure A)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : Ω × A → ℝ) (M b : ℝ) (hF : Measurable F)
    (hbound : ∀ z, |F z| ≤ M)
    (hosc : ∀ a x y, |F (x, a) - F (y, a)| ≤ b) (t : ℝ) :
    Integrable (fun z => Real.exp (t * (F z - ∫ y, F (y, z.2) ∂μ))) (μ.prod ν) := by
  apply integrable_exp_mul_of_mem_Icc (a := -b) (b := b)
    (hF.sub ((measurable_integral_fiber μ F hF).comp measurable_snd)).aemeasurable
  exact Filter.Eventually.of_forall (fun z =>
    abs_le.mp (abs_centered_fiber_le μ F M b hF hbound hosc z.2 z.1))

/-- One independent fiber contributes the Hoeffding factor to the full centered MGF. -/
theorem integral_exp_sub_integral_le_fiber (μ : Measure Ω) (ν : Measure A)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : Ω × A → ℝ) (M b : ℝ) (_hM : 0 ≤ M) (hb : 0 ≤ b) (hF : Measurable F)
    (hbound : ∀ z, |F z| ≤ M)
    (hosc : ∀ a x y, |F (x, a) - F (y, a)| ≤ b) (t : ℝ) :
    (∫ z, Real.exp (t * (F z - ∫ w, F w ∂μ.prod ν)) ∂μ.prod ν) ≤
      Real.exp (b ^ 2 * t ^ 2 / 2) *
        ∫ a, Real.exp (t * ((∫ x, F (x, a) ∂μ) - ∫ w, F w ∂μ.prod ν)) ∂ν := by
  let G : A → ℝ := fun a => ∫ x, F (x, a) ∂μ
  let c : ℝ := ∫ a, G a ∂ν
  have hmean : c = ∫ z, F z ∂μ.prod ν :=
    integral_integral_fiber μ ν F M hF hbound
  rw [← hmean]
  have hprod := integrable_exp_prod_sub_const μ ν F M hF hbound c t
  have havg := integrable_exp_integral_fiber_sub_const μ ν F M hF hbound c t
  have hsplit (a : A) :
      (∫ x, Real.exp (t * (F (x, a) - c)) ∂μ) =
        (∫ x, Real.exp (t * (F (x, a) - G a)) ∂μ) * Real.exp (t * (G a - c)) := by
    calc
      _ = ∫ x, Real.exp (t * (F (x, a) - G a)) * Real.exp (t * (G a - c)) ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => by
          dsimp only
          rw [← Real.exp_add]
          congr 1
          ring)
      _ = _ := integral_mul_const _ _
  calc
    _ = ∫ a, ∫ x, Real.exp (t * (F (x, a) - c)) ∂μ ∂ν :=
      integral_prod_symm _ hprod
    _ ≤ ∫ a, Real.exp (b ^ 2 * t ^ 2 / 2) * Real.exp (t * (G a - c)) ∂ν := by
      apply integral_mono hprod.integral_prod_right (havg.const_mul _)
      intro a
      change (∫ x, Real.exp (t * (F (x, a) - c)) ∂μ) ≤
        Real.exp (b ^ 2 * t ^ 2 / 2) * Real.exp (t * (G a - c))
      rw [hsplit a]
      exact mul_le_mul_of_nonneg_right
        (integral_exp_centered_fiber_le μ F M b hb hF hbound hosc a t)
        (Real.exp_nonneg _)
    _ = _ := integral_const_mul _ _

end LPPDifferentiability
