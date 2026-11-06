/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.BirkhoffL1

/-! # Backward and centered Birkhoff averages

Finite reversal transfers the integral absolute error of forward averages to
backward averages. Inverse Birkhoff and uniqueness in L1 identify the same
constant almost everywhere. No ergodicity assumption is used.
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace LPPDifferentiability

/-- The average of `f (T^(-j) ω)` for `j = 1, ..., n`, zero at `n = 0`. -/
@[expose] noncomputable def backwardBirkhoffAverage {Ω : Type*} [MeasurableSpace Ω]
    (T : Ω ≃ᵐ Ω) (f : Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  birkhoffAverage ℝ T.symm (f ∘ T.symm) n

/-- The average of the forward and backward averages, with `2n` terms. -/
@[expose] noncomputable def centeredBirkhoffAverage {Ω : Type*} [MeasurableSpace Ω]
    (T : Ω ≃ᵐ Ω) (f : Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (birkhoffAverage ℝ T f n ω + backwardBirkhoffAverage T f n ω) / 2

/-- The backward convention has precisely the indices `1, ..., n`. -/
theorem backwardBirkhoffAverage_eq_sum {Ω : Type*} [MeasurableSpace Ω]
    (T : Ω ≃ᵐ Ω) (f : Ω → ℝ) (n : ℕ) (ω : Ω) :
    backwardBirkhoffAverage T f n ω =
      (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, f (((T.symm : Ω → Ω)^[j + 1]) ω) := by
  simp only [backwardBirkhoffAverage, birkhoffAverage, birkhoffSum,
    Function.comp_apply, Function.iterate_succ_apply', smul_eq_mul]

private theorem backward_sum_reversal {Ω : Type*} [MeasurableSpace Ω]
    (T : Ω ≃ᵐ Ω) (f : Ω → ℝ) (n : ℕ) (ω : Ω) :
    birkhoffSum T.symm (f ∘ T.symm) n (((T : Ω → Ω)^[n]) ω) =
      birkhoffSum T f n ω := by
  induction n with
  | zero => simp only [birkhoffSum_zero_apply]
  | succ n ih =>
    rw [birkhoffSum_succ_apply', Function.comp_apply,
      Function.iterate_succ_apply', T.symm_apply_apply,
      birkhoffSum_succ_apply, ih, add_comm]

/-- Finite reversal, including the harmless zeroth average. -/
theorem backwardBirkhoffAverage_iterate {Ω : Type*} [MeasurableSpace Ω]
    (T : Ω ≃ᵐ Ω) (f : Ω → ℝ) (n : ℕ) (ω : Ω) :
    backwardBirkhoffAverage T f n (((T : Ω → Ω)^[n]) ω) =
      birkhoffAverage ℝ T f n ω := by
  exact congrArg (fun a : ℝ => (n : ℝ)⁻¹ • a) (backward_sum_reversal T f n ω)

/-- Backward averages are genuinely integrable. -/
theorem integrable_backwardBirkhoffAverage {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {T : Ω ≃ᵐ Ω} {f : Ω → ℝ}
    (hT : MeasurePreserving T μ μ) (hi : Integrable f μ) (n : ℕ) :
    Integrable (backwardBirkhoffAverage T f n) μ :=
  integrable_birkhoffAverage (hT.symm T) ((hT.symm T).integrable_comp_of_integrable hi) n

/-- Centered averages are genuinely integrable. -/
theorem integrable_centeredBirkhoffAverage {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {T : Ω ≃ᵐ Ω} {f : Ω → ℝ}
    (hT : MeasurePreserving T μ μ) (hi : Integrable f μ) (n : ℕ) :
    Integrable (centeredBirkhoffAverage T f n) μ :=
  ((integrable_birkhoffAverage hT hi n).add
    (integrable_backwardBirkhoffAverage hT hi n)).div_const 2

private theorem measurableEmbedding_iterate {Ω : Type*} [MeasurableSpace Ω]
    (T : Ω ≃ᵐ Ω) (n : ℕ) : MeasurableEmbedding ((T : Ω → Ω)^[n]) := by
  induction n with
  | zero => exact MeasurableEmbedding.id
  | succ n ih =>
    rw [Function.iterate_succ']
    exact T.measurableEmbedding.comp ih

/-- The errors are integrable before applying change of variables. -/
theorem integral_abs_backwardBirkhoffAverage_sub_const {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω ≃ᵐ Ω} {f : Ω → ℝ}
    (hT : MeasurePreserving T μ μ) (hi : Integrable f μ) (q : ℝ) (n : ℕ) :
    (∫ ω, |backwardBirkhoffAverage T f n ω - q| ∂μ) =
      ∫ ω, |birkhoffAverage ℝ T f n ω - q| ∂μ := by
  have hbi : Integrable (fun ω => |backwardBirkhoffAverage T f n ω - q|) μ :=
    ((integrable_backwardBirkhoffAverage hT hi n).sub (integrable_const q)).abs
  have hfi : Integrable (fun ω => |birkhoffAverage ℝ T f n ω - q|) μ :=
    ((integrable_birkhoffAverage hT hi n).sub (integrable_const q)).abs
  have heq := (hT.iterate n).integral_comp (measurableEmbedding_iterate T n)
    (fun ω => |backwardBirkhoffAverage T f n ω - q|)
  simpa only [backwardBirkhoffAverage_iterate] using heq.symm

private theorem birkhoffAverage_congr_ae {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {T : Ω → Ω} {f f' : Ω → ℝ}
    (hT : MeasurePreserving T μ μ) (heq : f =ᵐ[μ] f') :
    ∀ᵐ ω ∂μ, ∀ n, birkhoffAverage ℝ T f n ω = birkhoffAverage ℝ T f' n ω := by
  have horbit : ∀ᵐ ω ∂μ, ∀ j : ℕ, f ((T^[j]) ω) = f' ((T^[j]) ω) :=
    ae_all_iff.mpr fun j => (hT.iterate j).quasiMeasurePreserving.ae heq
  filter_upwards [horbit] with ω hω
  intro n
  simp only [birkhoffAverage, birkhoffSum, hω]

private theorem exists_birkhoffL1_of_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω} {f : Ω → ℝ}
    (hT : MeasurePreserving T μ μ) (hi : Integrable f μ) :
    ∃ g : Ω → ℝ, Integrable g μ ∧
      (∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => birkhoffAverage ℝ T f n ω) atTop (𝓝 (g ω))) ∧
      Tendsto (fun n : ℕ => ∫ ω, |birkhoffAverage ℝ T f n ω - g ω| ∂μ)
        atTop (𝓝 0) := by
  let f' := hi.aestronglyMeasurable.mk f
  have heq : f =ᵐ[μ] f' := hi.aestronglyMeasurable.ae_eq_mk
  obtain ⟨g, _, hgi, hgc, _, _, hgL1⟩ := exists_birkhoffL1 hT
    hi.aestronglyMeasurable.measurable_mk (hi.congr heq)
  have havg := birkhoffAverage_congr_ae hT heq
  refine ⟨g, hgi, ?_, ?_⟩
  · filter_upwards [havg, hgc] with ω hω hgω
    simpa only [hω] using hgω
  · apply hgL1.congr'
    exact Eventually.of_forall fun n => integral_congr_ae
      (havg.mono fun ω hω => congrArg (fun a : ℝ => |a - g ω|) (hω n).symm)

/-- Forward L1 convergence to a constant forces backward almost sure and L1
convergence to the same constant. No forward almost sure premise is needed. -/
theorem backwardBirkhoffAverage_tendsto_const {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω ≃ᵐ Ω} {f : Ω → ℝ}
    (hT : MeasurePreserving T μ μ) (hi : Integrable f μ) (q : ℝ)
    (hL1 : Tendsto (fun n : ℕ => ∫ ω, |birkhoffAverage ℝ T f n ω - q| ∂μ)
      atTop (𝓝 0)) :
    (∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => backwardBirkhoffAverage T f n ω) atTop (𝓝 q)) ∧
    Tendsto (fun n : ℕ => ∫ ω, |backwardBirkhoffAverage T f n ω - q| ∂μ)
      atTop (𝓝 0) := by
  have hbL1 : Tendsto (fun n : ℕ => ∫ ω, |backwardBirkhoffAverage T f n ω - q| ∂μ)
      atTop (𝓝 0) := by
    simpa only [integral_abs_backwardBirkhoffAverage_sub_const hT hi q] using hL1
  obtain ⟨g, hgi, hgc, hgL1⟩ := exists_birkhoffL1_of_integrable (hT.symm T)
    ((hT.symm T).integrable_comp_of_integrable hi)
  change (∀ᵐ ω ∂μ, Tendsto (fun n => backwardBirkhoffAverage T f n ω) atTop
    (𝓝 (g ω))) at hgc
  change Tendsto (fun n => ∫ ω, |backwardBirkhoffAverage T f n ω - g ω| ∂μ)
    atTop (𝓝 0) at hgL1
  have hbound (n : ℕ) : (∫ ω, |g ω - q| ∂μ) ≤
      (∫ ω, |backwardBirkhoffAverage T f n ω - g ω| ∂μ) +
      ∫ ω, |backwardBirkhoffAverage T f n ω - q| ∂μ := by
    have hbi := integrable_backwardBirkhoffAverage hT hi n
    have hbg : Integrable (fun ω => |backwardBirkhoffAverage T f n ω - g ω|) μ :=
      (hbi.sub hgi).abs
    have hbq : Integrable (fun ω => |backwardBirkhoffAverage T f n ω - q|) μ :=
      (hbi.sub (integrable_const q)).abs
    rw [← integral_add hbg hbq]
    apply integral_mono ((hgi.sub (integrable_const q)).abs)
      (((hbi.sub hgi).abs).add ((hbi.sub (integrable_const q)).abs))
    intro ω
    calc
      |g ω - q| ≤ |g ω - backwardBirkhoffAverage T f n ω| +
          |backwardBirkhoffAverage T f n ω - q| := abs_sub_le _ _ _
      _ = _ := by rw [abs_sub_comm (g ω)]; rfl
  have hzero : (∫ ω, |g ω - q| ∂μ) = 0 := by
    apply le_antisymm _ (integral_nonneg fun ω => abs_nonneg _)
    have hz := hgL1.add hbL1
    simp only [add_zero] at hz
    exact ge_of_tendsto hz (Eventually.of_forall hbound)
  have heq : ∀ᵐ ω ∂μ, g ω = q := by
    have hz := (integral_eq_zero_iff_of_nonneg
      (fun ω => abs_nonneg (g ω - q)) ((hgi.sub (integrable_const q)).abs)).mp hzero
    filter_upwards [hz] with ω hω
    exact sub_eq_zero.mp (abs_eq_zero.mp hω)
  refine ⟨?_, hbL1⟩
  filter_upwards [hgc, heq] with ω hω heqω
  simpa only [heqω] using hω

/-- Forward almost sure and L1 convergence to a constant yields both conclusions
for the actual centered averages. -/
theorem centeredBirkhoffAverage_tendsto_const {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω ≃ᵐ Ω} {f : Ω → ℝ}
    (hT : MeasurePreserving T μ μ) (hi : Integrable f μ) (q : ℝ)
    (hae : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => birkhoffAverage ℝ T f n ω) atTop (𝓝 q))
    (hL1 : Tendsto (fun n : ℕ => ∫ ω, |birkhoffAverage ℝ T f n ω - q| ∂μ)
      atTop (𝓝 0)) :
    (∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => centeredBirkhoffAverage T f n ω) atTop (𝓝 q)) ∧
    Tendsto (fun n : ℕ => ∫ ω, |centeredBirkhoffAverage T f n ω - q| ∂μ)
      atTop (𝓝 0) := by
  obtain ⟨hbae, hbL1⟩ := backwardBirkhoffAverage_tendsto_const hT hi q hL1
  refine ⟨?_, ?_⟩
  · filter_upwards [hae, hbae] with ω hf hb
    have h := (hf.add hb).div_const 2
    simpa only [centeredBirkhoffAverage, add_self_div_two] using h
  · have hbound (n : ℕ) : (∫ ω, |centeredBirkhoffAverage T f n ω - q| ∂μ) ≤
        ((∫ ω, |birkhoffAverage ℝ T f n ω - q| ∂μ) +
          ∫ ω, |backwardBirkhoffAverage T f n ω - q| ∂μ) / 2 := by
      have hfi := integrable_birkhoffAverage hT hi n
      have hbi := integrable_backwardBirkhoffAverage hT hi n
      have hfq : Integrable (fun ω => |birkhoffAverage ℝ T f n ω - q|) μ :=
        (hfi.sub (integrable_const q)).abs
      have hbq : Integrable (fun ω => |backwardBirkhoffAverage T f n ω - q|) μ :=
        (hbi.sub (integrable_const q)).abs
      rw [← integral_add hfq hbq, ← integral_div]
      apply integral_mono
        ((integrable_centeredBirkhoffAverage hT hi n).sub (integrable_const q)).abs
        ((((hfi.sub (integrable_const q)).abs).add
          ((hbi.sub (integrable_const q)).abs)).div_const 2)
      intro ω
      change |(birkhoffAverage ℝ T f n ω + backwardBirkhoffAverage T f n ω) / 2 - q| ≤ _
      have heq : (birkhoffAverage ℝ T f n ω + backwardBirkhoffAverage T f n ω) / 2 - q =
          ((birkhoffAverage ℝ T f n ω - q) + (backwardBirkhoffAverage T f n ω - q)) / 2 := by ring
      rw [heq, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)
    have hz := (hL1.add hbL1).div_const 2
    simp only [add_zero, zero_div] at hz
    exact squeeze_zero (fun n => integral_nonneg fun ω => abs_nonneg _) hbound hz

end LPPDifferentiability
