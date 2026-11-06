/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.NegativeMomentBounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Interval
import Mathlib.Order.Filter.AtTopBot.Field

/-!
# Strict negative-threshold mass

The actual negative-part moment bounds strict lower tails. For the threshold
`-(η s / (64 K))`, the probability of the retained half-line eventually exceeds
one half for every probability law, independently of its moments.
-/

@[expose] public section

open MeasureTheory
open Set Filter
open scoped ENNReal Topology

namespace LPPDifferentiability

/-- The actual negative-part moment gives the strict lower-tail Markov bound.
The event is open at `-T`, so atoms at the threshold need no separate treatment. -/
theorem measureReal_Iio_neg_rpow_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (T p : ℝ)
    (hT : 0 < T) (hp : 1 < p)
    (hmoment : (∫⁻ x, ENNReal.ofReal ((max (-x) 0) ^ p) ∂μ) < ∞) :
    μ.real (Iio (-T)) ≤
      (∫ x, (max (-x) 0) ^ p ∂μ) * T ^ (-p) := by
  have hp0 : 0 ≤ p := le_trans (by norm_num : (0 : ℝ) ≤ 1) hp.le
  have hnonneg (x : ℝ) : 0 ≤ (max (-x) 0) ^ p :=
    Real.rpow_nonneg (le_max_right _ _) p
  have hpower : Integrable (fun x : ℝ => (max (-x) 0) ^ p) μ := by
    refine ⟨((continuous_id.neg.max continuous_const).rpow_const
      (fun _ => Or.inr hp0)).aestronglyMeasurable, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall hnonneg)).2 hmoment
  have hmarkov :
      T ^ p * μ.real {x : ℝ | T ^ p ≤ (max (-x) 0) ^ p} ≤
        ∫ x, (max (-x) 0) ^ p ∂μ :=
    mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall hnonneg) hpower (T ^ p)
  have hsubset : Iio (-T) ⊆ {x : ℝ | T ^ p ≤ (max (-x) 0) ^ p} := by
    intro x hx
    change T ^ p ≤ (max (-x) 0) ^ p
    change x < -T at hx
    have hx' : T < -x := by linarith
    have hnegx : 0 < -x := lt_trans hT hx'
    rw [max_eq_left hnegx.le]
    exact Real.rpow_le_rpow hT.le hx'.le hp0
  have hbound :
      T ^ p * μ.real (Iio (-T)) ≤ ∫ x, (max (-x) 0) ^ p ∂μ := by
    calc
      T ^ p * μ.real (Iio (-T)) ≤
          T ^ p * μ.real {x : ℝ | T ^ p ≤ (max (-x) 0) ^ p} :=
        mul_le_mul_of_nonneg_left (measureReal_mono hsubset)
          (Real.rpow_nonneg hT.le p)
      _ ≤ _ := hmarkov
  have hTpow : 0 < T ^ p := Real.rpow_pos_of_pos hT p
  calc
    μ.real (Iio (-T)) ≤
        (∫ x, (max (-x) 0) ^ p ∂μ) / T ^ p :=
      (le_div_iff₀ hTpow).2 (by simpa only [mul_comm] using hbound)
    _ = (∫ x, (max (-x) 0) ^ p ∂μ) * T ^ (-p) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg hT.le p]

/-- The strict-tail estimate at the threshold `-(η s / (64 K))`, with coefficient
`(64 * K / η)^p`. -/
theorem measureReal_Iio_sourceScale_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (η K p s : ℝ)
    (hη : 0 < η) (hK : 1 ≤ K) (hp : 1 < p) (hs : 0 < s)
    (hmoment : (∫⁻ x, ENNReal.ofReal ((max (-x) 0) ^ p) ∂μ) < ∞) :
    μ.real (Iio (-(η * s / (64 * K))) ) ≤
      (∫ x, (max (-x) 0) ^ p ∂μ) * (64 * K / η) ^ p * s ^ (-p) := by
  have hden : 0 < 64 * K := by positivity
  have hT : 0 < η * s / (64 * K) := by positivity
  have htail := measureReal_Iio_neg_rpow_le μ (η * s / (64 * K)) p hT hp hmoment
  have hfactorization : η * s / (64 * K) = (η / (64 * K)) * s := by
    field_simp [ne_of_gt hden]
  have hpower :
      (η * s / (64 * K)) ^ (-p) = (64 * K / η) ^ p * s ^ (-p) := by
    rw [hfactorization, Real.mul_rpow (by positivity) hs.le,
      Real.div_rpow hη.le (by positivity) (-p),
      Real.rpow_neg hη.le p, Real.rpow_neg (by positivity) p,
      Real.div_rpow (by positivity) hη.le p]
    have hηpow : η ^ p ≠ 0 := (Real.rpow_pos_of_pos hη p).ne'
    have hdenpow : (64 * K) ^ p ≠ 0 :=
      (Real.rpow_pos_of_pos hden p).ne'
    field_simp [hηpow, hdenpow]
  calc
    μ.real (Iio (-(η * s / (64 * K)))) ≤
        (∫ x, (max (-x) 0) ^ p ∂μ) * (η * s / (64 * K)) ^ (-p) := htail
    _ = (∫ x, (max (-x) 0) ^ p ∂μ) *
        ((64 * K / η) ^ p * s ^ (-p)) := by rw [hpower]
    _ = (∫ x, (max (-x) 0) ^ p ∂μ) * (64 * K / η) ^ p * s ^ (-p) := by
      rw [mul_assoc]

/-- Along the threshold `-(η s / (64 K))`, an actual probability law eventually assigns
at least half its mass to `[-ηs/(64K), ∞)`, without any moment assumption. -/
theorem eventually_measure_Ici_sourceScale_ge_half
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (η K : ℝ)
    (hη : 0 < η) (hK : 1 ≤ K) :
    ∀ᶠ s : ℝ in atTop,
      (2 : ℝ≥0∞)⁻¹ ≤ μ (Ici (-(η * s / (64 * K)))) := by
  have hden : 0 < 64 * K := by positivity
  have hcoeff : 0 < η / (64 * K) := div_pos hη hden
  have hscale : Tendsto (fun s : ℝ => (η / (64 * K)) * s) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hcoeff).2 tendsto_id
  have hratio (s : ℝ) : η * s / (64 * K) = (η / (64 * K)) * s := by
    field_simp [ne_of_gt hden]
  have hthreshold : Tendsto (fun s : ℝ => -(η * s / (64 * K))) atTop atBot := by
    simpa only [Function.comp_def, hratio] using tendsto_neg_atTop_atBot.comp hscale
  have hmass :
      Tendsto (fun s : ℝ => μ (Ici (-(η * s / (64 * K)))) ) atTop (𝓝 1) := by
    simpa only [Function.comp_def, measure_univ] using
      (tendsto_measure_Ici_atBot μ).comp hthreshold
  exact (hmass.eventually_const_lt (by norm_num)).mono fun _ hs => le_of_lt hs

end LPPDifferentiability
