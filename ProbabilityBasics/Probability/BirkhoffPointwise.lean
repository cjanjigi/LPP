/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.BirkhoffSignedLimits
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Pointwise Birkhoff theorem with preserved mean

The signed invariant-threshold proof in Keane-Petersen,
arXiv:math/0608251v1, printed pp.249-250. L1 convergence is separate.
-/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace LPPDifferentiability

private theorem integral_upper_rep_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω} {f u : Ω → ℝ}
    (hT : MeasurePreserving T μ μ) (hm : Measurable f) (hi : Integrable f μ)
    (hum : Measurable u) (hui : Integrable u μ)
    (hueq : ∀ᵐ ω ∂μ, (u ω : EReal) = birkhoffUpper T f ω)
    (huinv : ∀ᵐ ω ∂μ, u (T ω) = u ω) :
    (∫ ω, u ω ∂μ) ≤ ∫ ω, f ω ∂μ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let threshold : Ω → ℝ := fun ω => u ω - ε
  have htm : Measurable threshold := hum.sub measurable_const
  have hti : Integrable threshold μ := hui.sub (integrable_const ε)
  have htinv : ∀ᵐ ω ∂μ, threshold (T ω) = threshold ω := by
    filter_upwards [huinv] with ω hω
    exact congrArg (fun a : ℝ => a - ε) hω
  have hE : ∀ᵐ ω ∂μ, ω ∈ maximalEvent T f threshold := by
    filter_upwards [hueq] with ω hω
    apply mem_maximalEvent_of_lt_birkhoffUpper
    rw [← hω]
    exact EReal.coe_lt_coe (sub_lt_self _ hε)
  have hb := integral_maximalEvent_nonneg hT hm htm hi hti htinv
  rw [← integral_eq_setIntegral hE (fun ω => f ω - threshold ω), integral_sub hi hti] at hb
  have htint : (∫ ω, threshold ω ∂μ) = (∫ ω, u ω ∂μ) - ε := by
    simp only [threshold, integral_sub hui (integrable_const ε), integral_const,
      measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
  rw [htint] at hb
  linarith only [hb]

/-- The actual forward averages of an integrable measurable real observable
converge almost surely to an integrable invariant function with the same mean.
No ergodicity or invertibility is assumed. -/
theorem exists_birkhoffPointwise {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω} {f : Ω → ℝ}
    (hT : MeasurePreserving T μ μ) (hm : Measurable f) (hi : Integrable f μ) :
    ∃ g : Ω → ℝ, Measurable g ∧ Integrable g μ ∧
      (∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => birkhoffAverage ℝ T f n ω) atTop (𝓝 (g ω))) ∧
      (∀ᵐ ω ∂μ, g (T ω) = g ω) ∧ (∫ ω, g ω ∂μ) = ∫ ω, f ω ∂μ := by
  obtain ⟨u, l, hum, hui, hlm, hli, hueq, hleq, huinv, hlinv, hlu⟩ :=
    exists_integrable_birkhoffSignedLimits hT hm hi
  have huf : (∫ ω, u ω ∂μ) ≤ ∫ ω, f ω ∂μ :=
    integral_upper_rep_le hT hm hi hum hui hueq huinv
  have hnegEq : ∀ᵐ ω ∂μ, ((-l ω : ℝ) : EReal) = birkhoffUpper T (-f) ω := by
    filter_upwards [hleq] with ω hω
    rw [EReal.coe_neg, hω, birkhoffUpper_neg]
  have hnegInv : ∀ᵐ ω ∂μ, (-l) (T ω) = (-l) ω := by
    filter_upwards [hlinv] with ω hω
    exact congrArg Neg.neg hω
  have hneg := integral_upper_rep_le hT hm.neg hi.neg hlm.neg hli.neg hnegEq hnegInv
  simp only [Pi.neg_apply, integral_neg] at hneg
  have hfl : (∫ ω, f ω ∂μ) ≤ ∫ ω, l ω ∂μ := neg_le_neg_iff.mp hneg
  have hluInt : (∫ ω, l ω ∂μ) ≤ ∫ ω, u ω ∂μ := integral_mono_ae hli hui hlu
  have hmean : (∫ ω, u ω ∂μ) = ∫ ω, f ω ∂μ := le_antisymm huf (hfl.trans hluInt)
  have hzero : (∫ ω, u ω - l ω ∂μ) = 0 := by
    rw [integral_sub hui hli]
    exact sub_eq_zero.mpr (le_antisymm (huf.trans hfl) hluInt)
  have hdiff : ∀ᵐ ω ∂μ, 0 ≤ u ω - l ω := by
    filter_upwards [hlu] with ω hω
    exact sub_nonneg.mpr hω
  have heqZero := (integral_eq_zero_iff_of_nonneg_ae hdiff (hui.sub hli)).mp hzero
  have hul : ∀ᵐ ω ∂μ, u ω = l ω := by
    filter_upwards [heqZero] with ω hω
    exact sub_eq_zero.mp hω
  refine ⟨u, hum, hui, ?_, huinv, hmean⟩
  filter_upwards [hueq, hleq, hul] with ω hu hl heq
  apply EReal.tendsto_coe.mp
  refine tendsto_of_liminf_eq_limsup ?_ ?_ (by isBoundedDefault) (by isBoundedDefault)
  · change birkhoffLower T f ω = (u ω : EReal)
    rw [← hl, heq]
  · exact hu.symm

end LPPDifferentiability
