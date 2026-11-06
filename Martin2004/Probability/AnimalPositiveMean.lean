/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.AnimalLayerCakeExpectation
public import Martin2004.Probability.AnimalMaximum
public import Martin2004.Probability.AnimalThresholdBridge
public import Martin2004.Probability.BernoulliAnimalMean
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Positive animal means under an integrated square-root tail

Layer cake and the actual strict-threshold Bernoulli field give one universal
constant for the extended expectation bound. A finite integrated square-root
tail then gives genuine integrability and the real expectation bound with the
same constant. No finite-tail hypothesis is needed for the extended bound.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace LPPDifferentiability

/-- The square root of a real event probability agrees with the extended
one-half power. No regularity assumption on the event is needed. -/
theorem ofReal_sqrt_measureReal (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (s : Set ℝ) :
    ENNReal.ofReal (Real.sqrt (μ.real s)) = (μ s) ^ (1 / 2 : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg measureReal_nonneg
    (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top μ s)]

/-- For the actual positive-part field, Tonelli bounds its expected maximum
by the integral of the expected actual strict-threshold maximum. -/
theorem expected_positive_animalMaximum_le_lintegral_expected_threshold
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) (hn : 1 ≤ n) :
    (∫⁻ ω : Environment,
      ENNReal.ofReal (animalMaximum n hn (fun v => max (ω v) 0)) ∂environmentLaw μ) ≤
    ∫⁻ t in Ioi (0 : ℝ), ∫⁻ ω : Environment,
      ENNReal.ofReal (animalMaximum n hn (strictThresholdField t ω)) ∂environmentLaw μ := by
  classical
  let H := (animalFamily_finite n).toFinset
  have hH : H.Nonempty :=
    (animalFamily_finite n).toFinset_nonempty.mpr (animalFamily_nonempty n hn)
  have hlayer := expected_finite_animalWeightMaximum_le_lintegral_thresholdMaximum
    (μ := environmentLaw μ) H hH (fun (ω : Environment) v => max (ω v) 0)
    (fun v => (measurable_environment_eval v).max measurable_const)
    (fun ω v => le_max_right (ω v) 0)
  calc
    _ = ∫⁻ ω : Environment,
        H.sup' hH (fun U => ∑ v ∈ U, ENNReal.ofReal (max (ω v) 0)) ∂environmentLaw μ := by
      apply lintegral_congr
      intro ω
      exact animalMaximum_ofReal_eq_sup'_sum_ofReal n hn _ (fun v => le_max_right _ _)
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), ∫⁻ ω : Environment,
        animalThresholdMaximum H hH (fun v => max (ω v) 0) t ∂environmentLaw μ := hlayer
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      apply lintegral_congr
      intro ω
      rw [animalThresholdMaximum_positivePart H hH ω t ht.le]
      exact animalThresholdMaximum_eq_ofReal_animalMaximum n hn ω t

/-- One constant bounds the extended expected positive animal maximum for
all original laws and sizes. Under the actual finite square-root tail,
the same constant gives integrability and the ordinary expectation bound. -/
theorem exists_positive_animalMaximum_mean_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ]
      (n : ℕ) (hn : 1 ≤ n),
      (∫⁻ ω : Environment,
        ENNReal.ofReal (animalMaximum n hn (fun v => max (ω v) 0)) ∂environmentLaw μ) ≤
        ENNReal.ofReal (C * n) *
          (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) ∧
      ((∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞ →
        Integrable (fun ω : Environment => animalMaximum n hn (fun v => max (ω v) 0))
          (environmentLaw μ) ∧
        (∫ ω : Environment, animalMaximum n hn (fun v => max (ω v) 0) ∂environmentLaw μ) ≤
          C * n * (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)).toReal) := by
  obtain ⟨C, hC, hmean⟩ := exists_pos_universal_animalMaximum_mean_bound
  refine ⟨C, hC, ?_⟩
  intro μ _ n hn
  have hthreshold (t : ℝ) :
      (∫⁻ ω : Environment,
        ENNReal.ofReal (animalMaximum n hn (strictThresholdField t ω)) ∂environmentLaw μ) ≤
      ENNReal.ofReal (C * n) * (μ (Ioi t)) ^ (1 / 2 : ℝ) := by
    obtain ⟨hi, hb⟩ := hmean (environmentLaw μ)
      (fun (v : Lattice) (ω : Environment) => strictThresholdField t ω v)
      (iIndepFun_strictThresholdField_eval μ t)
      (measurable_strictThresholdField_eval t)
      (fun v => Filter.Eventually.of_forall fun ω => strictThresholdField_zero_or_one t ω v)
      (μ.real (Ioi t)) (strictThresholdField_eval_oneProbability μ t)
      measureReal_nonneg measureReal_le_one n hn
    have hnn (ω : Environment) : 0 ≤ animalMaximum n hn (strictThresholdField t ω) :=
      animalMaximum_nonneg_of_forall_nonneg n hn _ (strictThresholdField_nonneg t ω)
    calc
      _ = ENNReal.ofReal (∫ ω : Environment,
          animalMaximum n hn (strictThresholdField t ω) ∂environmentLaw μ) :=
        (ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hnn)).symm
      _ ≤ ENNReal.ofReal (C * n * Real.sqrt (μ.real (Ioi t))) :=
        ENNReal.ofReal_le_ofReal hb
      _ = _ := by
        rw [ENNReal.ofReal_mul (mul_nonneg hC.le (Nat.cast_nonneg n)),
          ofReal_sqrt_measureReal μ (Ioi t)]
  have hbound :
      (∫⁻ ω : Environment,
        ENNReal.ofReal (animalMaximum n hn (fun v => max (ω v) 0)) ∂environmentLaw μ) ≤
      ENNReal.ofReal (C * n) *
        (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) := by
    calc
      _ ≤ ∫⁻ t in Ioi (0 : ℝ), ∫⁻ ω : Environment,
          ENNReal.ofReal (animalMaximum n hn (strictThresholdField t ω)) ∂environmentLaw μ :=
        expected_positive_animalMaximum_le_lintegral_expected_threshold μ n hn
      _ ≤ ∫⁻ t in Ioi (0 : ℝ),
          ENNReal.ofReal (C * n) * (μ (Ioi t)) ^ (1 / 2 : ℝ) :=
        lintegral_mono hthreshold
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  refine ⟨hbound, ?_⟩
  intro hpos
  have hm := measurable_animalMaximum
    (fun (v : Lattice) (ω : Environment) => max (ω v) 0)
    (fun v => (measurable_environment_eval v).max measurable_const) n hn
  have hnn : ∀ ω : Environment, 0 ≤ animalMaximum n hn (fun v => max (ω v) 0) :=
    fun ω => animalMaximum_nonneg_of_forall_nonneg n hn _ (fun v => le_max_right _ _)
  have hf : (∫⁻ ω : Environment,
      ENNReal.ofReal (animalMaximum n hn (fun v => max (ω v) 0)) ∂environmentLaw μ) < ∞ :=
    hbound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hpos)
  have hi : Integrable (fun ω : Environment => animalMaximum n hn (fun v => max (ω v) 0))
      (environmentLaw μ) :=
    ⟨hm.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hnn)).2 hf⟩
  refine ⟨hi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hnn)] at hbound
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hpos.ne) hbound
  simpa only [ENNReal.toReal_ofReal (integral_nonneg hnn), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (mul_nonneg hC.le (Nat.cast_nonneg n))] using hreal

end LPPDifferentiability
