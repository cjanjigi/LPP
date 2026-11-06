/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.ConditionalNegativeMoments
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Conditional light and heavy negative parts

Split the actual negative part at a strict heavy threshold and its weak light
complement, under the same normalized restriction used for the conditional
moment bounds.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace LPPDifferentiability

/-- The strict heavy part and weak light part sum to the actual negative part,
including at equality with the threshold. -/
theorem conditionalNegativeSplit_add (b x : ℝ) :
    (if b < max (-x) 0 then max (-x) 0 else 0) +
      (if max (-x) 0 ≤ b then max (-x) 0 else 0) = max (-x) 0 := by
  by_cases h : max (-x) 0 ≤ b
  · simp [h, not_lt_of_ge h]
  · simp [h, not_le.mp h]

/-- The weak-threshold light part lies between zero and its cutoff. -/
theorem conditionalLightPart_bounds (b : ℝ) (hb : 0 ≤ b) (x : ℝ) :
    0 ≤ (if max (-x) 0 ≤ b then max (-x) 0 else 0) ∧
      (if max (-x) 0 ≤ b then max (-x) 0 else 0) ≤ b := by
  by_cases h : max (-x) 0 ≤ b
  · simp [h]
  · simp [h, hb]

/-- The literal light part is measurable. -/
theorem measurable_conditionalLightPart (b : ℝ) :
    Measurable (fun x : ℝ =>
      if max (-x) 0 ≤ b then max (-x) 0 else 0) := by
  apply Measurable.ite
  · exact measurableSet_le
      ((continuous_id.neg.max continuous_const).measurable) measurable_const
  · exact (continuous_id.neg.max continuous_const).measurable
  · exact measurable_const

/-- The actual heavy part is nonnegative and bounded by (T) almost surely
under the same normalized restriction. -/
theorem ae_conditionalHeavyPart_bounds
    (μ : Measure ℝ) (T b : ℝ) (hT : 0 < T) :
    ∀ᵐ x ∂((μ (Set.Ici (-T)))⁻¹ • μ.restrict (Set.Ici (-T))),
      0 ≤ (if b < max (-x) 0 then max (-x) 0 else 0) ∧
        (if b < max (-x) 0 then max (-x) 0 else 0) ≤ T := by
  let ν : Measure ℝ := (μ (Set.Ici (-T)))⁻¹ • μ.restrict (Set.Ici (-T))
  let H : ℝ → ℝ := fun x => if b < max (-x) 0 then max (-x) 0 else 0
  change ∀ᵐ x ∂ν, 0 ≤ H x ∧ H x ≤ T
  have hsupport := ae_conditionalNegativeRestriction_ge μ T
  filter_upwards [hsupport] with x hx
  have hyT : max (-x) 0 ≤ T := max_le (by linarith) (le_of_lt hT)
  constructor
  · dsimp [H]
    split_ifs <;> positivity
  · dsimp [H]
    split_ifs
    · exact hyT
    · exact le_of_lt hT

/-- The literal light part is integrable under the actual conditional law,
with integrability derived from the original negative-part moment. -/
theorem integrable_conditionalLightPart_of_lintegral_lt_top
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (T p b : ℝ) (hp : 1 < p)
    (hthreshold : (2 : ℝ≥0∞)⁻¹ ≤ μ (Set.Ici (-T))) (hb : 0 < b)
    (hmoment : (∫⁻ x, ENNReal.ofReal ((max (-x) 0) ^ p) ∂μ) < ∞) :
    Integrable (fun x : ℝ =>
      if max (-x) 0 ≤ b then max (-x) 0 else 0)
      ((μ (Set.Ici (-T)))⁻¹ • μ.restrict (Set.Ici (-T))) := by
  let ν : Measure ℝ := (μ (Set.Ici (-T)))⁻¹ • μ.restrict (Set.Ici (-T))
  let Z : ℝ → ℝ := fun x => if max (-x) 0 ≤ b then max (-x) 0 else 0
  let : IsProbabilityMeasure ν := by
    dsimp [ν]
    exact conditionalNegativeRestriction_isProbabilityMeasure μ T hthreshold
  change Integrable Z ν
  have hY : Integrable (fun x : ℝ => max (-x) 0) ν :=
    integrable_conditionalNegativePart_of_lintegral_lt_top μ T p hp hthreshold hmoment
  have hZmeas : Measurable Z := by
    dsimp [Z]
    exact measurable_conditionalLightPart b
  have hZnonneg : ∀ x, 0 ≤ Z x := by
    intro x
    exact (conditionalLightPart_bounds b (le_of_lt hb) x).1
  have hZleY : Z ≤ fun x => max (-x) 0 := by
    intro x
    dsimp [Z]
    split_ifs <;> simp
  exact hY.mono_nonneg hZmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall hZnonneg) (Filter.Eventually.of_forall hZleY)

/-- The conditional light-part mean is bounded by twice the original
negative-part mean. -/
theorem integral_conditionalLightPart_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (T p b : ℝ) (hp : 1 < p)
    (hthreshold : (2 : ℝ≥0∞)⁻¹ ≤ μ (Set.Ici (-T))) (hb : 0 < b)
    (hmoment : (∫⁻ x, ENNReal.ofReal ((max (-x) 0) ^ p) ∂μ) < ∞) :
    (∫ x, (if max (-x) 0 ≤ b then max (-x) 0 else 0)
      ∂((μ (Set.Ici (-T)))⁻¹ • μ.restrict (Set.Ici (-T)))) ≤
        2 * (∫ x, max (-x) 0 ∂μ) := by
  let ν : Measure ℝ := (μ (Set.Ici (-T)))⁻¹ • μ.restrict (Set.Ici (-T))
  let Z : ℝ → ℝ := fun x => if max (-x) 0 ≤ b then max (-x) 0 else 0
  let : IsProbabilityMeasure ν := by
    dsimp [ν]
    exact conditionalNegativeRestriction_isProbabilityMeasure μ T hthreshold
  have hZ : Integrable Z ν :=
    integrable_conditionalLightPart_of_lintegral_lt_top μ T p b hp hthreshold hb hmoment
  have hY : Integrable (fun x : ℝ => max (-x) 0) ν :=
    integrable_conditionalNegativePart_of_lintegral_lt_top μ T p hp hthreshold hmoment
  have hZleY : Z ≤ fun x => max (-x) 0 := by
    intro x
    dsimp [Z]
    split_ifs <;> simp
  calc
    (∫ x, Z x ∂ν) ≤ ∫ x, max (-x) 0 ∂ν :=
      integral_mono hZ hY hZleY
    _ ≤ 2 * (∫ x, max (-x) 0 ∂μ) :=
      integral_conditionalNegativePart_le μ T p hp hthreshold hmoment

/-- The conditional light-part second moment follows from (Z^2\le bZ),
not from a variance assumption on the original weights. -/
theorem integral_conditionalLightPart_sq_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (T p b : ℝ) (hp : 1 < p)
    (hthreshold : (2 : ℝ≥0∞)⁻¹ ≤ μ (Set.Ici (-T))) (hb : 0 < b)
    (hmoment : (∫⁻ x, ENNReal.ofReal ((max (-x) 0) ^ p) ∂μ) < ∞) :
    (∫ x, (if max (-x) 0 ≤ b then max (-x) 0 else 0) ^ 2
      ∂((μ (Set.Ici (-T)))⁻¹ • μ.restrict (Set.Ici (-T)))) ≤
        2 * (∫ x, max (-x) 0 ∂μ) * b := by
  let ν : Measure ℝ := (μ (Set.Ici (-T)))⁻¹ • μ.restrict (Set.Ici (-T))
  let Z : ℝ → ℝ := fun x => if max (-x) 0 ≤ b then max (-x) 0 else 0
  let : IsProbabilityMeasure ν := by
    dsimp [ν]
    exact conditionalNegativeRestriction_isProbabilityMeasure μ T hthreshold
  have hZ : Integrable Z ν :=
    integrable_conditionalLightPart_of_lintegral_lt_top μ T p b hp hthreshold hb hmoment
  have hZsq : Integrable (fun x => Z x ^ 2) ν := by
    refine (integrable_const (b ^ 2)).mono ?_ ?_
    · fun_prop
    · filter_upwards [] with x
      rw [Real.norm_of_nonneg (sq_nonneg (Z x)),
        Real.norm_of_nonneg (sq_nonneg b)]
      have hZx : 0 ≤ Z x ∧ Z x ≤ b := by
        change 0 ≤ (if max (-x) 0 ≤ b then max (-x) 0 else 0) ∧
          (if max (-x) 0 ≤ b then max (-x) 0 else 0) ≤ b
        exact conditionalLightPart_bounds b (le_of_lt hb) x
      have hprod : 0 ≤ (b - Z x) * (b + Z x) :=
        mul_nonneg (sub_nonneg.mpr hZx.2) (by linarith [hZx.1, hb])
      nlinarith [hprod]
  have hZmul : Integrable (fun x => b * Z x) ν := hZ.const_mul b
  have hZsq_le : ∀ x, Z x ^ 2 ≤ b * Z x := by
    intro x
    have hZx : 0 ≤ Z x ∧ Z x ≤ b := by
      change 0 ≤ (if max (-x) 0 ≤ b then max (-x) 0 else 0) ∧
        (if max (-x) 0 ≤ b then max (-x) 0 else 0) ≤ b
      exact conditionalLightPart_bounds b (le_of_lt hb) x
    simpa only [pow_two] using mul_le_mul_of_nonneg_right hZx.2 hZx.1
  have hmean := integral_conditionalLightPart_le μ T p b hp hthreshold hb hmoment
  calc
    (∫ x, Z x ^ 2 ∂ν) ≤ ∫ x, b * Z x ∂ν :=
      integral_mono hZsq hZmul (fun x => hZsq_le x)
    _ = b * (∫ x, Z x ∂ν) := integral_const_mul b Z
    _ ≤ b * (2 * (∫ x, max (-x) 0 ∂μ)) :=
      mul_le_mul_of_nonneg_left hmean (le_of_lt hb)
    _ = 2 * (∫ x, max (-x) 0 ∂μ) * b := by ring

end LPPDifferentiability
