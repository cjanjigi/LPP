/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.NegativeMomentBounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Conditional negative-part moments

Normalize the literal restriction of a probability law to a lower half-line.
The conditional negative-part mean and strict-tail estimates follow from the
actual negative-part moment of the original law.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace LPPDifferentiability

/-- The normalized restriction to `[-T, ∞)` has total mass one. -/
theorem conditionalNegativeRestriction_isProbabilityMeasure
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (T : ℝ)
    (hthreshold : (2 : ℝ≥0∞)⁻¹ ≤ μ (Set.Ici (-T))) :
    IsProbabilityMeasure ((μ (Set.Ici (-T)))⁻¹ • μ.restrict (Set.Ici (-T))) := by
  have hqpos : (0 : ℝ≥0∞) < μ (Set.Ici (-T)) :=
    lt_of_lt_of_le (by norm_num) hthreshold
  have hqtop : μ (Set.Ici (-T)) ≠ ∞ := measure_ne_top μ _
  refine ⟨?_⟩
  rw [Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  exact ENNReal.inv_mul_cancel hqpos.ne' hqtop

/-- The actual normalized restriction is dominated by twice the original law. -/
theorem conditionalNegativeRestriction_le_two
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (T : ℝ)
    (hthreshold : (2 : ℝ≥0∞)⁻¹ ≤ μ (Set.Ici (-T))) :
    (μ (Set.Ici (-T)))⁻¹ • μ.restrict (Set.Ici (-T)) ≤ (2 : ℝ≥0∞) • μ := by
  have hqinv : (μ (Set.Ici (-T)))⁻¹ ≤ (2 : ℝ≥0∞) := by
    calc
      (μ (Set.Ici (-T)))⁻¹ ≤ ((2 : ℝ≥0∞)⁻¹)⁻¹ :=
        (ENNReal.inv_le_inv).2 hthreshold
      _ = 2 := by simp
  have hrestrict : μ.restrict (Set.Ici (-T)) ≤ μ := Measure.restrict_le_self
  refine Measure.le_iff'.2 fun s => ?_
  rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
  calc
    (μ (Set.Ici (-T)))⁻¹ * (μ.restrict (Set.Ici (-T))) s ≤
        2 * (μ.restrict (Set.Ici (-T))) s :=
      mul_le_mul_of_nonneg_right hqinv (by positivity)
    _ ≤ 2 * μ s :=
      mul_le_mul_of_nonneg_left (hrestrict s) (by positivity)

/-- The normalized restriction is supported on its conditioning half-line. -/
theorem ae_conditionalNegativeRestriction_ge
    (μ : Measure ℝ) (T : ℝ) :
    ∀ᵐ x ∂((μ (Set.Ici (-T)))⁻¹ • μ.restrict (Set.Ici (-T))), -T ≤ x := by
  have hA : ∀ᵐ x ∂((μ (Set.Ici (-T)))⁻¹ • μ.restrict (Set.Ici (-T))),
      x ∈ Set.Ici (-T) :=
    Measure.ae_smul_measure (ae_restrict_mem measurableSet_Ici) _
  filter_upwards [hA] with x hx
  exact hx

/-- A finite actual negative-part moment above order one gives conditional
integrability, without assuming the desired conditional mean bound. -/
theorem integrable_conditionalNegativePart_of_lintegral_lt_top
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (T p : ℝ) (hp : 1 < p)
    (hthreshold : (2 : ℝ≥0∞)⁻¹ ≤ μ (Set.Ici (-T)))
    (hmoment : (∫⁻ x, ENNReal.ofReal ((max (-x) 0) ^ p) ∂μ) < ∞) :
    Integrable (fun x : ℝ => max (-x) 0)
      ((μ (Set.Ici (-T)))⁻¹ • μ.restrict (Set.Ici (-T))) := by
  let ν : Measure ℝ := (μ (Set.Ici (-T)))⁻¹ • μ.restrict (Set.Ici (-T))
  let : IsProbabilityMeasure ν := by
    dsimp [ν]
    exact conditionalNegativeRestriction_isProbabilityMeasure μ T hthreshold
  have hμ : Integrable (fun x : ℝ => max (-x) 0) μ :=
    integrable_negativePart_of_lintegral_lt_top μ p hp hmoment
  have hlarge : Integrable (fun x : ℝ => max (-x) 0) ((2 : ℝ≥0∞) • μ) :=
    hμ.smul_measure (by norm_num)
  exact hlarge.mono_measure (conditionalNegativeRestriction_le_two μ T hthreshold)

/-- The conditional mean of the actual negative part is at most twice its
unconditioned mean. Both means are Bochner integrals of `max (-x) 0`. -/
theorem integral_conditionalNegativePart_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (T p : ℝ) (hp : 1 < p)
    (hthreshold : (2 : ℝ≥0∞)⁻¹ ≤ μ (Set.Ici (-T)))
    (hmoment : (∫⁻ x, ENNReal.ofReal ((max (-x) 0) ^ p) ∂μ) < ∞) :
    (∫ x, max (-x) 0 ∂((μ (Set.Ici (-T)))⁻¹ • μ.restrict (Set.Ici (-T)))) ≤
      2 * (∫ x, max (-x) 0 ∂μ) := by
  let ν : Measure ℝ := (μ (Set.Ici (-T)))⁻¹ • μ.restrict (Set.Ici (-T))
  let : IsProbabilityMeasure ν := by
    dsimp [ν]
    exact conditionalNegativeRestriction_isProbabilityMeasure μ T hthreshold
  have hνle := conditionalNegativeRestriction_le_two μ T hthreshold
  have hμ : Integrable (fun x : ℝ => max (-x) 0) μ :=
    integrable_negativePart_of_lintegral_lt_top μ p hp hmoment
  have hlarge : Integrable (fun x : ℝ => max (-x) 0) ((2 : ℝ≥0∞) • μ) :=
    hμ.smul_measure (by norm_num)
  have hν : Integrable (fun x : ℝ => max (-x) 0) ν := hlarge.mono_measure hνle
  have hnonneg : 0 ≤ᵐ[((2 : ℝ≥0∞) • μ)] fun x : ℝ => max (-x) 0 :=
    Filter.Eventually.of_forall fun _ => le_max_right _ _
  calc
    (∫ x, max (-x) 0 ∂ν) ≤ ∫ x, max (-x) 0 ∂((2 : ℝ≥0∞) • μ) :=
      integral_mono_measure hνle hnonneg hlarge
    _ = 2 * (∫ x, max (-x) 0 ∂μ) := by simp

/-- The strict conditional tail is bounded by the actual original negative
moment, with no tail estimate supplied as an input. -/
theorem conditionalNegativePart_strict_tail_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (T p b : ℝ) (hp : 1 < p)
    (hthreshold : (2 : ℝ≥0∞)⁻¹ ≤ μ (Set.Ici (-T))) (hb : 0 < b)
    (hmoment : (∫⁻ x, ENNReal.ofReal ((max (-x) 0) ^ p) ∂μ) < ∞) :
    (((μ (Set.Ici (-T)))⁻¹ • μ.restrict (Set.Ici (-T))).real
      {x : ℝ | max (-x) 0 > b}) ≤
      2 * (∫ x, (max (-x) 0) ^ p ∂μ) * b ^ (-p) := by
  let ν : Measure ℝ := (μ (Set.Ici (-T)))⁻¹ • μ.restrict (Set.Ici (-T))
  let : IsProbabilityMeasure ν := by
    dsimp [ν]
    exact conditionalNegativeRestriction_isProbabilityMeasure μ T hthreshold
  have hνle := conditionalNegativeRestriction_le_two μ T hthreshold
  have hp0 : 0 ≤ p := le_trans (by norm_num : (0 : ℝ) ≤ 1) hp.le
  have hpower : Integrable (fun x : ℝ => (max (-x) 0) ^ p) μ := by
    refine ⟨((continuous_id.neg.max continuous_const).rpow_const
      (fun _ => Or.inr hp0)).aestronglyMeasurable, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (le_max_right _ _) p)).2 hmoment
  have hpowerLarge : Integrable (fun x : ℝ => (max (-x) 0) ^ p)
      ((2 : ℝ≥0∞) • μ) := hpower.smul_measure (by norm_num)
  have hpowerNu : Integrable (fun x : ℝ => (max (-x) 0) ^ p) ν :=
    hpowerLarge.mono_measure hνle
  have hpowerMean :
      (∫ x, (max (-x) 0) ^ p ∂ν) ≤
        2 * (∫ x, (max (-x) 0) ^ p ∂μ) := by
    have hnonneg : 0 ≤ᵐ[((2 : ℝ≥0∞) • μ)] fun x : ℝ => (max (-x) 0) ^ p :=
      Filter.Eventually.of_forall fun x => Real.rpow_nonneg (le_max_right _ _) p
    calc
      (∫ x, (max (-x) 0) ^ p ∂ν) ≤
          ∫ x, (max (-x) 0) ^ p ∂((2 : ℝ≥0∞) • μ) :=
        integral_mono_measure hνle hnonneg hpowerLarge
      _ = 2 * (∫ x, (max (-x) 0) ^ p ∂μ) := by simp
  have hmarkov :
      b ^ p * ν.real {x : ℝ | b ^ p ≤ (max (-x) 0) ^ p} ≤
        ∫ x, (max (-x) 0) ^ p ∂ν :=
    mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (le_max_right _ _) p)
      hpowerNu (b ^ p)
  have hsubset : {x : ℝ | max (-x) 0 > b} ⊆
      {x : ℝ | b ^ p ≤ (max (-x) 0) ^ p} := by
    intro x hx
    exact Real.rpow_le_rpow (le_of_lt hb) (le_of_lt hx) hp0
  have hbound :
      b ^ p * ν.real {x : ℝ | max (-x) 0 > b} ≤
        2 * (∫ x, (max (-x) 0) ^ p ∂μ) := by
    calc
      b ^ p * ν.real {x : ℝ | max (-x) 0 > b} ≤
          b ^ p * ν.real {x : ℝ | b ^ p ≤ (max (-x) 0) ^ p} :=
        mul_le_mul_of_nonneg_left (measureReal_mono hsubset) (Real.rpow_nonneg (le_of_lt hb) p)
      _ ≤ ∫ x, (max (-x) 0) ^ p ∂ν := hmarkov
      _ ≤ 2 * (∫ x, (max (-x) 0) ^ p ∂μ) := hpowerMean
  have hbpow : 0 < b ^ p := Real.rpow_pos_of_pos hb p
  have hbound' :
      ν.real {x : ℝ | max (-x) 0 > b} * b ^ p ≤
        2 * (∫ x, (max (-x) 0) ^ p ∂μ) :=
    (mul_comm _ _).trans_le hbound
  have hfinal : ν.real {x : ℝ | max (-x) 0 > b} ≤
      (2 * (∫ x, (max (-x) 0) ^ p ∂μ)) / b ^ p :=
    (le_div_iff₀ hbpow).2 hbound'
  calc
    ν.real {x : ℝ | max (-x) 0 > b} ≤
        (2 * (∫ x, (max (-x) 0) ^ p ∂μ)) / b ^ p := hfinal
    _ = 2 * (∫ x, (max (-x) 0) ^ p ∂μ) * b ^ (-p) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg (le_of_lt hb) p]

end LPPDifferentiability
