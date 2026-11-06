/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.BirkhoffUpper
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! # Integrability of the nonnegative upper orbit-average limit

The monotone-convergence conclusion of the invariant-threshold argument on
Keane–Petersen, arXiv:math/0608251v1, printed p.250.
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace LPPDifferentiability

/-- Monotone convergence of the actual clips bounds the extended upper limit's integral. -/
theorem lintegral_birkhoffUpper_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω} {h : Ω → ℝ}
    (hT : MeasurePreserving T μ μ) (hm : Measurable h) (hi : Integrable h μ)
    (hh : ∀ ω, 0 ≤ h ω) :
    (∫⁻ ω, (birkhoffUpper T h ω).toENNReal ∂μ) ≤ ENNReal.ofReal (∫ ω, h ω ∂μ) := by
  let c := birkhoffUpperClip T h hh
  have hcm (n : ℕ) : Measurable (c n) := measurable_birkhoffUpperClip hT.measurable hm hh n
  have hci (n : ℕ) : Integrable (c n) μ := integrable_birkhoffUpperClip hT.measurable hm hh n
  have hcn (n : ℕ) (ω : Ω) : 0 ≤ c n ω := ERealTruncation.trunc_nonneg _ _
  have hmono : ∀ᵐ ω ∂μ, Monotone (fun n => ENNReal.ofReal (c n ω)) := by
    apply Eventually.of_forall
    intro ω m n hmn
    exact ENNReal.ofReal_le_ofReal (ERealTruncation.monotone_trunc_level _ hmn)
  have hpoint : ∀ᵐ ω ∂μ, Tendsto (fun n => ENNReal.ofReal (c n ω)) atTop
      (𝓝 (birkhoffUpper T h ω).toENNReal) := by
    apply Eventually.of_forall
    intro ω
    simpa only [Function.comp_def, EReal.real_coe_toENNReal, c, birkhoffUpperClip] using
      EReal.continuous_toENNReal.continuousAt.tendsto.comp
        (ERealTruncation.tendsto_coe_trunc_level
          ⟨birkhoffUpper T h ω, birkhoffUpper_nonneg T h hh ω⟩)
  have hlimit := lintegral_tendsto_of_tendsto_of_monotone
    (fun n => (hcm n).ennreal_ofReal.aemeasurable) hmono hpoint
  have hright : Tendsto (fun n : ℕ => ENNReal.ofReal
      ((∫ ω, h ω ∂μ) + 1 / ((n : ℝ) + 1))) atTop
      (𝓝 (ENNReal.ofReal (∫ ω, h ω ∂μ))) := by
    apply ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    simpa only [add_zero] using
      (tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  apply le_of_tendsto_of_tendsto hlimit hright
  apply Eventually.of_forall
  intro n
  change (∫⁻ ω, ENNReal.ofReal (c n ω) ∂μ) ≤
    ENNReal.ofReal ((∫ ω, h ω ∂μ) + 1 / ((n : ℝ) + 1))
  rw [← ofReal_integral_eq_lintegral_ofReal (hci n) (Eventually.of_forall (hcn n))]
  exact ENNReal.ofReal_le_ofReal (integral_birkhoffUpperClip_le hT hm hi hh n)

/-- Finiteness is derived from the clip estimates, rather than assumed. -/
theorem ae_birkhoffUpper_ne_top {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω} {h : Ω → ℝ}
    (hT : MeasurePreserving T μ μ) (hm : Measurable h) (hi : Integrable h μ)
    (hh : ∀ ω, 0 ≤ h ω) : ∀ᵐ ω ∂μ, birkhoffUpper T h ω ≠ ⊤ := by
  have hfinite : (∫⁻ ω, (birkhoffUpper T h ω).toENNReal ∂μ) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (lintegral_birkhoffUpper_le hT hm hi hh)
  filter_upwards [ae_lt_top (measurable_birkhoffUpper hT.measurable hm).ereal_toENNReal hfinite]
    with ω hω
  exact EReal.toENNReal_ne_top_iff.mp hω.ne

/-- An integrable real representative of the actual nonnegative upper limit,
with its invariant mean bound. The exceptional set is proved null first. -/
theorem exists_integrable_birkhoffUpper {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω} {h : Ω → ℝ}
    (hT : MeasurePreserving T μ μ) (hm : Measurable h) (hi : Integrable h μ)
    (hh : ∀ ω, 0 ≤ h ω) :
    ∃ g : Ω → ℝ, Measurable g ∧ Integrable g μ ∧
      (∀ᵐ ω ∂μ, 0 ≤ g ω) ∧
      (∀ᵐ ω ∂μ, (g ω : EReal) = birkhoffUpper T h ω) ∧
      (∀ᵐ ω ∂μ, g (T ω) = g ω) ∧ (∫ ω, g ω ∂μ) ≤ ∫ ω, h ω ∂μ := by
  have hUm := (measurable_birkhoffUpper hT.measurable hm).ereal_toENNReal
  have hbound := lintegral_birkhoffUpper_le hT hm hi hh
  have hfinite : (∫⁻ ω, (birkhoffUpper T h ω).toENNReal ∂μ) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound
  have hpointfinite := ae_lt_top hUm hfinite
  let g : Ω → ℝ := fun ω => (birkhoffUpper T h ω).toENNReal.toReal
  have hgm : Measurable g := hUm.ennreal_toReal
  have hgi : Integrable g μ := integrable_toReal_of_lintegral_ne_top hUm.aemeasurable hfinite
  have hgeq : ∀ᵐ ω ∂μ, (g ω : EReal) = birkhoffUpper T h ω := by
    filter_upwards [hpointfinite] with ω hω
    exact (EReal.coe_ennreal_toReal hω.ne).trans
      (EReal.coe_toENNReal (birkhoffUpper_nonneg T h hh ω))
  have hginv : ∀ᵐ ω ∂μ, g (T ω) = g ω := by
    filter_upwards [hT.quasiMeasurePreserving.ae hgeq, hgeq,
      ae_birkhoffUpper_invariant hT hi] with ω hshift hω hinv
    apply EReal.coe_injective
    exact hshift.trans (hinv.trans hω.symm)
  refine ⟨g, hgm, hgi, Eventually.of_forall (fun _ => ENNReal.toReal_nonneg), hgeq, hginv, ?_⟩
  rw [show (∫ ω, g ω ∂μ) = (∫⁻ ω, (birkhoffUpper T h ω).toENNReal ∂μ).toReal from
    integral_toReal hUm.aemeasurable hpointfinite]
  calc
    _ ≤ (ENNReal.ofReal (∫ ω, h ω ∂μ)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
    _ = ∫ ω, h ω ∂μ := ENNReal.toReal_ofReal (integral_nonneg hh)

end LPPDifferentiability
