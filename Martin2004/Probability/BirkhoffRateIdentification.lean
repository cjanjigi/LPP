/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.BilateralBirkhoff

/-! # Conditional identification of a Birkhoff rate

An actual sequence on the same probability space supplies a lower bound on
the Birkhoff limit. Its constant limit and the observable's mean bound identify
that limit without ergodicity. These are generic conditional helpers: an
application must still prove the actual sequence limit and finite domination.
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace LPPDifferentiability

/-- An integrable function above a constant with mean at most that constant
equals it almost everywhere on a probability space. -/
theorem ae_eq_const_of_integral_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {g : Ω → ℝ} {q : ℝ}
    (hi : Integrable g μ) (hlo : ∀ᵐ ω ∂μ, q ≤ g ω)
    (hmean : (∫ ω, g ω ∂μ) ≤ q) : ∀ᵐ ω ∂μ, g ω = q := by
  have hc : (∫ _ : Ω, q ∂μ) = q := by
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  have hge := integral_mono_ae (integrable_const q) hi hlo
  rw [hc] at hge
  have heq : (∫ _ : Ω, q ∂μ) = ∫ ω, g ω ∂μ := by
    rw [hc]
    exact le_antisymm hge hmean
  exact ((integral_eq_iff_of_ae_le (integrable_const q) hi hlo).mp heq).symm

/-- If the normalized actual sequence converges to `q` and is dominated by
every positive forward average of `f`, the mean bound identifies both forward
limits. The Birkhoff witness is produced internally; no ergodicity is needed. -/
theorem birkhoffAverage_tendsto_const_of_dominated_sequence
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → Ω} {f : Ω → ℝ} {A : ℕ → Ω → ℝ} {q : ℝ}
    (hT : MeasurePreserving T μ μ) (hm : Measurable f) (hi : Integrable f μ)
    (hmean : (∫ ω, f ω ∂μ) ≤ q)
    (hA : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => A n ω / (n : ℝ)) atTop (𝓝 q))
    (hdom : ∀ᵐ ω ∂μ, ∀ n : ℕ, 0 < n →
      A n ω / (n : ℝ) ≤ birkhoffAverage ℝ T f n ω) :
    (∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => birkhoffAverage ℝ T f n ω) atTop (𝓝 q)) ∧
    Tendsto (fun n : ℕ => ∫ ω, |birkhoffAverage ℝ T f n ω - q| ∂μ)
      atTop (𝓝 0) := by
  obtain ⟨g, _, hgi, hgc, _, hgmean, hgL1⟩ := exists_birkhoffL1 hT hm hi
  have hlo : ∀ᵐ ω ∂μ, q ≤ g ω := by
    filter_upwards [hA, hdom, hgc] with ω hAω hdomω hgcω
    apply le_of_tendsto_of_tendsto hAω hgcω
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact hdomω n hn
  have heq : ∀ᵐ ω ∂μ, g ω = q :=
    ae_eq_const_of_integral_le hgi hlo (hgmean.le.trans hmean)
  refine ⟨?_, ?_⟩
  · filter_upwards [hgc, heq] with ω hω heqω
    simpa only [heqω] using hω
  · apply hgL1.congr'
    exact Eventually.of_forall fun n => integral_congr_ae
      (heq.mono fun ω hω => congrArg (fun a : ℝ => |birkhoffAverage ℝ T f n ω - a|) hω)

/-- The same observable and rate have forward and actual centered AE and L1
limits, when an actual normalized sequence supplies the forward comparison. -/
theorem forward_centeredBirkhoffAverage_tendsto_const_of_dominated_sequence
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω ≃ᵐ Ω} {f : Ω → ℝ} {A : ℕ → Ω → ℝ} {q : ℝ}
    (hT : MeasurePreserving T μ μ) (hm : Measurable f) (hi : Integrable f μ)
    (hmean : (∫ ω, f ω ∂μ) ≤ q)
    (hA : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => A n ω / (n : ℝ)) atTop (𝓝 q))
    (hdom : ∀ᵐ ω ∂μ, ∀ n : ℕ, 0 < n →
      A n ω / (n : ℝ) ≤ birkhoffAverage ℝ T f n ω) :
    ((∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => birkhoffAverage ℝ T f n ω) atTop (𝓝 q)) ∧
      Tendsto (fun n : ℕ => ∫ ω, |birkhoffAverage ℝ T f n ω - q| ∂μ)
        atTop (𝓝 0)) ∧
    ((∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => centeredBirkhoffAverage T f n ω) atTop (𝓝 q)) ∧
      Tendsto (fun n : ℕ => ∫ ω, |centeredBirkhoffAverage T f n ω - q| ∂μ)
        atTop (𝓝 0)) := by
  have hf := birkhoffAverage_tendsto_const_of_dominated_sequence hT hm hi hmean hA hdom
  exact ⟨hf, centeredBirkhoffAverage_tendsto_const hT hi q hf.1 hf.2⟩

/-- All finite absolute errors used above are genuinely integrable, for any
real comparison constant, including the zeroth averages. -/
theorem integrable_forward_centeredBirkhoffAverage_abs_sub_const
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω ≃ᵐ Ω} {f : Ω → ℝ}
    (hT : MeasurePreserving T μ μ) (hi : Integrable f μ) (q : ℝ) (n : ℕ) :
    Integrable (fun ω => |birkhoffAverage ℝ T f n ω - q|) μ ∧
      Integrable (fun ω => |centeredBirkhoffAverage T f n ω - q|) μ :=
  ⟨((integrable_birkhoffAverage hT hi n).sub (integrable_const q)).abs,
    ((integrable_centeredBirkhoffAverage hT hi n).sub (integrable_const q)).abs⟩

end LPPDifferentiability
