/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.NonnegativeFourthMoment
public import ProbabilityBasics.Probability.PositiveMomentTail
public import LPP_Foundations.Probability.EnvironmentMap

/-!
# Fourth moments of finite sums of truncated environment weights

This file bounds the fourth moment of a finite sum of truncated weights `max (ω z - M) 0` under
the environment law, in terms of the single-site moments of the weights.
-/

public section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal

namespace LPPDifferentiability

/-- The elementary pointwise truncation estimate, for real exponents. -/
theorem truncated_positive_rpow_le (x : ℝ) {M p r : ℝ}
    (hM : 0 < M) (hr : 0 < r) (hrp : r ≤ p) :
    (max (x-M) 0)^r ≤ (max x 0)^p * M^(r-p) := by
  by_cases hx : x ≤ M
  · rw [max_eq_right (sub_nonpos.mpr hx), Real.zero_rpow hr.ne']
    positivity
  · have hMx : M < x := lt_of_not_ge hx
    have hx0 : 0 < x := hM.trans hMx
    rw [max_eq_left hx0.le]
    calc
      (max (x-M) 0)^r ≤ x^r := Real.rpow_le_rpow (le_max_right _ _)
        (max_le (by linarith only [hM]) hx0.le) hr.le
      _ = x^p * x^(r-p) := by rw [← Real.rpow_add hx0]; congr 1; ring
      _ ≤ x^p * M^(r-p) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hM hMx.le (sub_nonpos.mpr hrp))
        (Real.rpow_nonneg hx0.le p)

/-- The positive `p`-th moment of `μ` gives integrability of each truncated real power
`(max (x - M) 0)^r`, with no further moment assumption. -/
theorem integrable_truncated_positive_rpow (μ : Measure ℝ)
    {p r M : ℝ} (hp : 0 < p) (hr : 0 < r) (hrp : r ≤ p) (hM : 0 < M)
    (hmoment : (∫⁻ x, ENNReal.ofReal ((max x 0)^p) ∂μ) < ∞) :
    Integrable (fun x : ℝ => (max (x-M) 0)^r) μ := by
  have hi := (integrable_positive_rpow_of_lintegral_lt_top μ hp hmoment).mul_const
    (M^(r-p))
  apply hi.mono' (((Real.continuous_rpow_const hr.le).comp
    ((continuous_id.sub continuous_const).max continuous_const)).aestronglyMeasurable)
  exact Eventually.of_forall fun x => by
    change ‖(max (x-M) 0)^r‖ ≤ (max x 0)^p * M^(r-p)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (le_max_right _ _) r)]
    exact truncated_positive_rpow_le x hM hr hrp

/-- The integral of a truncated real power is bounded by the `p`-th moment of `μ` times
`M^(r - p)`. -/
theorem integral_truncated_positive_rpow_le (μ : Measure ℝ)
    {p r M : ℝ} (hp : 0 < p) (hr : 0 < r) (hrp : r ≤ p) (hM : 0 < M)
    (hmoment : (∫⁻ x, ENNReal.ofReal ((max x 0)^p) ∂μ) < ∞) :
    (∫ x : ℝ, (max (x-M) 0)^r ∂μ) ≤
      (∫ x : ℝ, (max x 0)^p ∂μ) * M^(r-p) := by
  rw [← integral_mul_const]
  exact integral_mono
    (integrable_truncated_positive_rpow μ hp hr hrp hM hmoment)
    ((integrable_positive_rpow_of_lintegral_lt_top μ hp hmoment).mul_const _)
    (fun x => truncated_positive_rpow_le x hM hr hrp)

/-- The fourth moment of the sum of truncated weights over any finite set of lattice sites
is bounded, with the explicit constant 34, by an expression in the size of the set and the
single-site moments of `μ`. -/
theorem excess_fourth_moment_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {p M : ℝ} (hp : 4 < p) (hM : 0 < M)
    (hmoment : (∫⁻ x, ENNReal.ofReal ((max x 0)^p) ∂μ) < ∞)
    (s : Finset Lattice) :
    (∫ ω : Environment, (∑ z ∈ s, max (ω z-M) 0)^4 ∂environmentLaw μ) ≤
      34*((s.card:ℝ)*(∫ x : ℝ, (max x 0)^p ∂μ)*M^(4-p)+
        ((s.card:ℝ)*(∫ x : ℝ, (max x 0)^p ∂μ)*M^(1-p))^4) := by
  let φ : ℝ → ℝ := fun x => max (x-M) 0
  have hφ : Measurable φ := (measurable_id.sub_const M).max measurable_const
  have hφ0 (x : ℝ) : 0 ≤ φ x := le_max_right _ _
  have hp0 : 0 < p := lt_trans (by norm_num) hp
  have hφ4 := integrable_truncated_positive_rpow μ hp0 (by norm_num : (0:ℝ)<4)
    hp.le hM hmoment
  have hmem : MemLp φ 4 μ := by
    apply (integrable_norm_rpow_iff hφ.aestronglyMeasurable (by norm_num : (4:ℝ≥0∞)≠0)
      (by norm_num : (4:ℝ≥0∞)≠∞)).mp
    simpa only [ENNReal.toReal_ofNat, Real.norm_eq_abs, abs_of_nonneg (hφ0 _)] using hφ4
  have hcoord (z : Lattice) : MeasurePreserving (fun ω : Environment => ω z)
      (environmentLaw μ) μ := ⟨measurable_environment_eval z, environmentLaw_map_eval μ z⟩
  have hmemz (z : Lattice) : MemLp (fun ω : Environment => φ (ω z)) 4 (environmentLaw μ) :=
    hmem.comp_measurePreserving (hcoord z)
  have hpow (z : Lattice) (k : ℕ) :
      (∫ ω : Environment, (φ (ω z))^k ∂environmentLaw μ) = ∫ x : ℝ, φ x^k ∂μ := by
    calc
      _ = ∫ x : ℝ, φ x^k ∂((environmentLaw μ).map (fun ω : Environment => ω z)) :=
        (integral_map (measurable_environment_eval z).aemeasurable
          (hφ.pow_const k).aestronglyMeasurable).symm
      _ = _ := by rw [environmentLaw_map_eval]
  have hbound1 := integral_truncated_positive_rpow_le μ hp0 (by norm_num : (0:ℝ)<1)
    (by linarith only [hp]) hM hmoment
  have hbound4 := integral_truncated_positive_rpow_le μ hp0 (by norm_num : (0:ℝ)<4)
    hp.le hM hmoment
  norm_num at hbound1 hbound4
  have hsum1 : (∑ z ∈ s, ∫ ω : Environment, φ (ω z) ∂environmentLaw μ) ≤
      (s.card:ℝ)*(∫ x : ℝ, (max x 0)^p ∂μ)*M^(1-p) := by
    calc
      _ = (s.card:ℝ)*(∫ x : ℝ, φ x ∂μ) := by
        simp_rw [show ∀ z : Lattice, (∫ ω : Environment, φ (ω z) ∂environmentLaw μ) =
          ∫ x : ℝ, φ x ∂μ from fun z => by simpa only [pow_one] using hpow z 1]
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := by simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hbound1 (Nat.cast_nonneg s.card)
  have hsum4 : (∑ z ∈ s, ∫ ω : Environment, (φ (ω z))^4 ∂environmentLaw μ) ≤
      (s.card:ℝ)*(∫ x : ℝ, (max x 0)^p ∂μ)*M^(4-p) := by
    calc
      _ = (s.card:ℝ)*(∫ x : ℝ, φ x^4 ∂μ) := by
        simp_rw [hpow]
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := by simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hbound4 (Nat.cast_nonneg s.card)
  have hsum0 : 0 ≤ ∑ z ∈ s, ∫ ω : Environment, φ (ω z) ∂environmentLaw μ :=
    Finset.sum_nonneg fun z _ => integral_nonneg fun ω => hφ0 _
  have hmean4 := pow_le_pow_left₀ hsum0 hsum1 4
  have hfinite := nonnegative_fourth_moment_le
    (fun z (ω : Environment) => φ (ω z)) hmemz
    (fun z => Eventually.of_forall fun ω => hφ0 (ω z))
    (iIndepFun_coordinatewise_environment_eval μ φ hφ) s
  change (∫ ω : Environment, (∑ z ∈ s, φ (ω z))^4 ∂environmentLaw μ) ≤ _
  linarith only [hfinite, hsum4, hmean4]

end LPPDifferentiability
