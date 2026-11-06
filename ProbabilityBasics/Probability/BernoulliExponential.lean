/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Probability.Independence.Integration

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Exponential moments for finite Bernoulli families

For a measurable zero-one random variable, the exponential moment is computed
from its actual one-site law. Independence then factors the moment for a fixed
finite set of distinct sites, and Markov's inequality gives its upper tail.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace LPPDifferentiability

/-- A measurable zero-one random variable has an integrable exponential. -/
theorem integrable_exp_of_ae_zero_or_one {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : Measurable X) (h01 : ∀ᵐ ω ∂μ, X ω = 0 ∨ X ω = 1) :
    Integrable (fun ω => Real.exp (X ω)) μ := by
  have hmeas : AEStronglyMeasurable (fun ω => Real.exp (X ω)) μ :=
    (Real.measurable_exp.comp hX).aestronglyMeasurable
  apply Integrable.of_bound hmeas (Real.exp 1)
  filter_upwards [h01] with ω hω
  have hnorm : ‖Real.exp (X ω)‖ = Real.exp (X ω) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  rw [hnorm]
  rcases hω with hzero | hone
  · rw [hzero]
    exact Real.exp_le_exp.mpr (by norm_num)
  · rw [hone]

/-- The exponential moment of one measurable zero-one variable, computed from
the measure of its one event. -/
theorem integral_exp_of_ae_zero_or_one {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : Measurable X) (h01 : ∀ᵐ ω ∂μ, X ω = 0 ∨ X ω = 1) :
    ∫ ω, Real.exp (X ω) ∂μ =
      1 - μ.real {ω | X ω = 1} + μ.real {ω | X ω = 1} * Real.exp 1 := by
  let A : Set Ω := {ω | X ω = 1}
  have hA : MeasurableSet A := by
    exact measurableSet_eq_fun hX measurable_const
  have hEq : (fun ω => Real.exp (X ω)) =ᵐ[μ]
      (fun ω => 1 + (Real.exp 1 - 1) * A.indicator (fun _ => (1 : ℝ)) ω) := by
    filter_upwards [h01] with ω hω
    rcases hω with hzero | hone
    · simp [A, hzero]
    · simp [A, hone]
  have hInd : Integrable (fun ω => A.indicator (fun _ => (1 : ℝ)) ω) μ :=
    (integrable_const 1).indicator hA
  have hCorr : Integrable
      (fun ω => (Real.exp 1 - 1) * A.indicator (fun _ => (1 : ℝ)) ω) μ :=
    hInd.const_mul (Real.exp 1 - 1)
  calc
    ∫ ω, Real.exp (X ω) ∂μ =
        ∫ ω, 1 + (Real.exp 1 - 1) * A.indicator (fun _ => (1 : ℝ)) ω ∂μ :=
      integral_congr_ae hEq
    _ = ∫ _ : Ω, (1 : ℝ) ∂μ +
        ∫ ω, (Real.exp 1 - 1) * A.indicator (fun _ => (1 : ℝ)) ω ∂μ :=
      integral_add (integrable_const 1) hCorr
    _ = μ.real Set.univ + (Real.exp 1 - 1) * μ.real A := by
      rw [integral_const, integral_const_mul, integral_indicator_const (1 : ℝ) hA]
      simp [Measure.real, measure_univ]
    _ = 1 - μ.real A + μ.real A * Real.exp 1 := by
      have hμ : μ.real Set.univ = 1 := by simp
      rw [hμ]
      ring

/-- The exponential of a finite sum of zero-one variables is integrable. The
sum and index set may both be empty. -/
theorem integrable_exp_finset_sum_of_ae_zero_or_one {Ω V : Type*}
    [MeasurableSpace Ω] [DecidableEq V] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Finset V) (X : V → Ω → ℝ)
    (hX : ∀ v : {x // x ∈ U}, Measurable (X v.1))
    (h01 : ∀ v : {x // x ∈ U}, ∀ᵐ ω ∂μ, X v.1 ω = 0 ∨ X v.1 ω = 1) :
    Integrable (fun ω => Real.exp (∑ v : {x // x ∈ U}, X v.1 ω)) μ := by
  classical
  have hmeas : Measurable
      (fun ω => ∑ v : {x // x ∈ U}, X v.1 ω) := by
    apply Finset.measurable_fun_sum
    intro v _
    exact hX v
  have hsm : AEStronglyMeasurable
      (fun ω => Real.exp (∑ v : {x // x ∈ U}, X v.1 ω)) μ :=
    (Real.measurable_exp.comp hmeas).aestronglyMeasurable
  apply Integrable.of_bound hsm (Real.exp (Fintype.card {x // x ∈ U}))
  filter_upwards [ae_all_iff.2 (fun v : {x // x ∈ U} => h01 v)] with ω hω
  have hsum_le : (∑ v : {x // x ∈ U}, X v.1 ω) ≤
      (Fintype.card {x // x ∈ U} : ℝ) := by
    calc
      (∑ v : {x // x ∈ U}, X v.1 ω) ≤ ∑ _v : {x // x ∈ U}, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro v hv
        rcases hω v with hzero | hone
        · rw [hzero]
          norm_num
        · rw [hone]
      _ = (Fintype.card {x // x ∈ U} : ℝ) := by simp
  have hnorm : ‖Real.exp (∑ v : {x // x ∈ U}, X v.1 ω)‖ =
      Real.exp (∑ v : {x // x ∈ U}, X v.1 ω) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  rw [hnorm]
  exact Real.exp_le_exp.mpr hsum_le

/-- For a fixed finite set of distinct sites, independence factors the actual
exponential moment of the sum. Every indexed site belongs to `U`, so this
statement does not count a site more than once. -/
theorem integral_exp_finset_sum_eq_pow {Ω V : Type*} [MeasurableSpace Ω]
    [DecidableEq V] (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Finset V)
    (X : V → Ω → ℝ) (p : ℝ)
    (hInd : iIndepFun (fun v : {x // x ∈ U} => X v.1) μ)
    (hX : ∀ v : {x // x ∈ U}, Measurable (X v.1))
    (h01 : ∀ v : {x // x ∈ U}, ∀ᵐ ω ∂μ, X v.1 ω = 0 ∨ X v.1 ω = 1)
    (hp : ∀ v : {x // x ∈ U}, μ.real {ω | X v.1 ω = 1} = p) :
    ∫ ω, Real.exp (∑ v : {x // x ∈ U}, X v.1 ω) ∂μ =
      (1 - p + p * Real.exp 1) ^ U.card := by
  classical
  have hIndExp : iIndepFun
      (fun v : {x // x ∈ U} => fun ω => Real.exp (X v.1 ω)) μ :=
    hInd.comp (fun _ => Real.exp) (fun _ => Real.measurable_exp)
  have hXexp : ∀ v : {x // x ∈ U},
      AEStronglyMeasurable (fun ω => Real.exp (X v.1 ω)) μ := by
    intro v
    exact (Real.measurable_exp.comp (hX v)).aestronglyMeasurable
  have hOne : ∀ v : {x // x ∈ U},
      ∫ ω, Real.exp (X v.1 ω) ∂μ = 1 - p + p * Real.exp 1 := by
    intro v
    rw [integral_exp_of_ae_zero_or_one μ (X v.1) (hX v) (h01 v)]
    rw [hp v]
  have hsum : (fun ω => Real.exp (∑ v : {x // x ∈ U}, X v.1 ω)) =
      (fun ω => ∏ v : {x // x ∈ U}, Real.exp (X v.1 ω)) := by
    funext ω
    rw [Real.exp_sum]
  calc
    ∫ ω, Real.exp (∑ v : {x // x ∈ U}, X v.1 ω) ∂μ =
        ∫ ω, ∏ v : {x // x ∈ U}, Real.exp (X v.1 ω) ∂μ := by
      rw [hsum]
    _ = ∏ v : {x // x ∈ U}, ∫ ω, Real.exp (X v.1 ω) ∂μ :=
      hIndExp.integral_fun_prod_eq_prod_integral hXexp
    _ = (1 - p + p * Real.exp 1) ^ U.card := by
      simp only [hOne, Finset.prod_const, Finset.card_univ, Fintype.card_coe]

/-- Exponential Markov bound for the sum on one fixed finite set of distinct
sites. The empty set is allowed; for `t > 0` its sum is zero. -/
theorem measureReal_finset_sum_ge_le_exp {Ω V : Type*} [MeasurableSpace Ω]
    [DecidableEq V] (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Finset V)
    (X : V → Ω → ℝ) (p t : ℝ)
    (hInd : iIndepFun (fun v : {x // x ∈ U} => X v.1) μ)
    (hX : ∀ v : {x // x ∈ U}, Measurable (X v.1))
    (h01 : ∀ v : {x // x ∈ U}, ∀ᵐ ω ∂μ, X v.1 ω = 0 ∨ X v.1 ω = 1)
    (hp : ∀ v : {x // x ∈ U}, μ.real {ω | X v.1 ω = 1} = p) (ht : 0 < t) :
    μ.real {ω | t ≤ ∑ v : {x // x ∈ U}, X v.1 ω} ≤
      Real.exp (-t) * (1 - p + p * Real.exp 1) ^ U.card := by
  have hIntegrable := integrable_exp_finset_sum_of_ae_zero_or_one μ U X hX h01
  have hMarkov := mul_meas_ge_le_integral_of_nonneg
    (f := fun ω => Real.exp (∑ v : {x // x ∈ U}, X v.1 ω))
    (Filter.Eventually.of_forall fun ω => Real.exp_nonneg _)
    hIntegrable (Real.exp t)
  have hEvent : {ω | Real.exp t ≤
      Real.exp (∑ v : {x // x ∈ U}, X v.1 ω)} =
      {ω | t ≤ ∑ v : {x // x ∈ U}, X v.1 ω} := by
    ext ω
    exact Real.exp_le_exp
  rw [hEvent, integral_exp_finset_sum_eq_pow μ U X p hInd hX h01 hp] at hMarkov
  have hExpGtOne : 1 < Real.exp t := by
    calc
      1 = Real.exp 0 := Real.exp_zero.symm
      _ < Real.exp t := Real.exp_lt_exp.mpr ht
  have hdiv : μ.real {ω | t ≤ ∑ v : {x // x ∈ U}, X v.1 ω} ≤
      (1 - p + p * Real.exp 1) ^ U.card / Real.exp t := by
    apply (le_div_iff₀ (lt_trans (by norm_num) hExpGtOne)).2
    simpa [mul_comm] using hMarkov
  calc
    μ.real {ω | t ≤ ∑ v : {x // x ∈ U}, X v.1 ω} ≤
        (1 - p + p * Real.exp 1) ^ U.card / Real.exp t := hdiv
    _ = Real.exp (-t) * (1 - p + p * Real.exp 1) ^ U.card := by
      rw [Real.exp_neg, div_eq_mul_inv]
      ring

end LPPDifferentiability
