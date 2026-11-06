/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.AverageInvariance
public import ProbabilityBasics.Probability.MaximalErgodic
public import ProbabilityBasics.Analysis.ERealTruncation
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-! # Truncated upper limits of nonnegative orbit averages

The invariant-threshold argument of Keane–Petersen, arXiv:math/0608251v1,
printed p.250. Finiteness of the extended upper limit is not assumed.
-/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace LPPDifferentiability

/-- The actual extended upper limit of the forward Birkhoff averages. -/
@[expose] noncomputable def birkhoffUpper {Ω : Type*} (T : Ω → Ω) (h : Ω → ℝ)
    (ω : Ω) : EReal :=
  limsup (fun n => ((birkhoffAverage ℝ T h n ω : ℝ) : EReal)) atTop

theorem measurable_birkhoffUpper {Ω : Type*} [MeasurableSpace Ω]
    {T : Ω → Ω} {h : Ω → ℝ} (hT : Measurable T) (hh : Measurable h) :
    Measurable (birkhoffUpper T h) := by
  apply Measurable.limsup
  intro n
  apply measurable_coe_real_ereal.comp
  unfold birkhoffAverage birkhoffSum
  exact (Finset.measurable_sum _ fun j _ => hh.comp (hT.iterate j)).const_smul ((n : ℝ)⁻¹)

theorem birkhoffUpper_nonneg {Ω : Type*} (T : Ω → Ω) (h : Ω → ℝ)
    (hh : ∀ ω, 0 ≤ h ω) (ω : Ω) : 0 ≤ birkhoffUpper T h ω := by
  refine le_limsup_of_frequently_le ?_ (by isBoundedDefault)
  apply Filter.Eventually.frequently
  apply Eventually.of_forall
  intro n
  apply EReal.coe_nonneg.mpr
  unfold birkhoffAverage birkhoffSum
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))
    (Finset.sum_nonneg fun j _ => hh ((T^[j]) ω))

theorem ae_birkhoffUpper_invariant {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω} {h : Ω → ℝ}
    (hT : MeasurePreserving T μ μ) (hh : Integrable h μ) :
    ∀ᵐ ω ∂μ, birkhoffUpper T h (T ω) = birkhoffUpper T h ω :=
  ae_limsup_birkhoffAverage_shift hT hh

/-- A strict real lower threshold for the upper limit is exceeded at a positive time. -/
theorem mem_maximalEvent_of_lt_birkhoffUpper {Ω : Type*} (T : Ω → Ω)
    (h threshold : Ω → ℝ) (ω : Ω)
    (hlt : (threshold ω : EReal) < birkhoffUpper T h ω) :
    ω ∈ maximalEvent T h threshold := by
  by_contra hn
  have hb : ∀ᶠ n : ℕ in atTop,
      ((birkhoffAverage ℝ T h n ω : ℝ) : EReal) ≤ (threshold ω : EReal) := by
    filter_upwards [eventually_ge_atTop 1] with n hn1
    apply EReal.coe_le_coe_iff.mpr
    apply le_of_not_gt
    intro ha
    apply hn
    refine ⟨n, hn1, ?_⟩
    simpa only [orbitAverage, birkhoffAverage, birkhoffSum, smul_eq_mul,
      div_eq_mul_inv, mul_comm] using ha
  exact (not_le_of_gt hlt) (limsup_le_of_le (by isBoundedDefault) hb)

/-- The real clip of the nonnegative extended upper limit. -/
@[expose] noncomputable def birkhoffUpperClip {Ω : Type*} (T : Ω → Ω)
    (h : Ω → ℝ) (hh : ∀ ω, 0 ≤ h ω) (n : ℕ) (ω : Ω) : ℝ :=
  ERealTruncation.trunc ⟨birkhoffUpper T h ω, birkhoffUpper_nonneg T h hh ω⟩
    (ERealTruncation.level n)

theorem measurable_birkhoffUpperClip {Ω : Type*} [MeasurableSpace Ω]
    {T : Ω → Ω} {h : Ω → ℝ} (hT : Measurable T) (hm : Measurable h)
    (hh : ∀ ω, 0 ≤ h ω) (n : ℕ) : Measurable (birkhoffUpperClip T h hh n) :=
  ERealTruncation.measurable_trunc_comp (measurable_birkhoffUpper hT hm)
    (birkhoffUpper_nonneg T h hh) (ERealTruncation.level n)

theorem integrable_birkhoffUpperClip {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω} {h : Ω → ℝ}
    (hT : Measurable T) (hm : Measurable h) (hh : ∀ ω, 0 ≤ h ω) (n : ℕ) :
    Integrable (birkhoffUpperClip T h hh n) μ := by
  apply (integrable_const ((n : ℝ) + 1)).mono'
    (measurable_birkhoffUpperClip hT hm hh n).aestronglyMeasurable
  apply Eventually.of_forall
  intro ω
  dsimp only [birkhoffUpperClip]
  rw [Real.norm_eq_abs, abs_of_nonneg (ERealTruncation.trunc_nonneg _ _)]
  exact ERealTruncation.trunc_le _ _

theorem integral_birkhoffUpperClip_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω} {h : Ω → ℝ}
    (hT : MeasurePreserving T μ μ) (hm : Measurable h) (hi : Integrable h μ)
    (hh : ∀ ω, 0 ≤ h ω) (n : ℕ) :
    (∫ ω, birkhoffUpperClip T h hh n ω ∂μ) ≤ (∫ ω, h ω ∂μ) + 1 / ((n : ℝ) + 1) := by
  let threshold := fun ω => birkhoffUpperClip T h hh n ω - 1 / ((n : ℝ) + 1)
  have hcm := measurable_birkhoffUpperClip hT.measurable hm hh n
  have hci : Integrable (birkhoffUpperClip T h hh n) μ :=
    integrable_birkhoffUpperClip hT.measurable hm hh n
  have hti : Integrable threshold μ := hci.sub (integrable_const _)
  have htm : Measurable threshold := hcm.sub measurable_const
  have htin : ∀ᵐ ω ∂μ, threshold (T ω) = threshold ω := by
    filter_upwards [ae_birkhoffUpper_invariant hT hi] with ω hω
    dsimp only [threshold, birkhoffUpperClip]
    congr 2
    exact Subtype.ext hω
  have hE : maximalEvent T h threshold = univ := by
    apply eq_univ_of_forall
    intro ω
    exact mem_maximalEvent_of_lt_birkhoffUpper T h threshold ω
      (ERealTruncation.threshold_lt _ n)
  have hb := integral_maximalEvent_nonneg hT hm htm hi hti htin
  rw [hE, setIntegral_univ, integral_sub hi hti] at hb
  have htint : (∫ ω, threshold ω ∂μ) =
      (∫ ω, birkhoffUpperClip T h hh n ω ∂μ) - 1 / ((n : ℝ) + 1) := by
    simp only [threshold, integral_sub hci (integrable_const _), integral_const,
      measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
  rw [htint] at hb
  linarith only [hb]

end LPPDifferentiability
