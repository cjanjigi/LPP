/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.BirkhoffPointwise
public import ProbabilityBasics.Probability.Scheffe

/-! # Birkhoff averages converge in integral absolute difference

The pointwise Keane–Petersen proof is supplemented by Scheffe convergence
for the averages of the positive and negative parts separately.
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace LPPDifferentiability

/-- Every actual finite forward average of an integrable function is integrable. -/
theorem integrable_birkhoffAverage {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {T : Ω → Ω} {f : Ω → ℝ}
    (hT : MeasurePreserving T μ μ) (hi : Integrable f μ) (n : ℕ) :
    Integrable (birkhoffAverage ℝ T f n) μ := by
  unfold birkhoffAverage birkhoffSum
  have hs : Integrable (fun ω => ∑ i ∈ Finset.range n, f ((T^[i]) ω)) μ :=
    integrable_finsetSum _ fun i _ => (hT.iterate i).integrable_comp_of_integrable hi
  simpa only [smul_eq_mul] using hs.const_mul (n : ℝ)⁻¹

/-- The mean normalization holds for positive lengths; the zeroth average is zero. -/
theorem integral_birkhoffAverage_of_pos {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {T : Ω → Ω} {f : Ω → ℝ}
    (hT : MeasurePreserving T μ μ) (hm : Measurable f) (hi : Integrable f μ)
    {n : ℕ} (hn : 0 < n) :
    (∫ ω, birkhoffAverage ℝ T f n ω ∂μ) = ∫ ω, f ω ∂μ := by
  have hcomp (i : ℕ) : (∫ ω, f ((T^[i]) ω) ∂μ) = ∫ ω, f ω ∂μ := by
    have h := integral_map_of_stronglyMeasurable (μ := μ)
      (hT.iterate i).measurable hm.stronglyMeasurable
    rw [(hT.iterate i).map_eq] at h
    exact h.symm
  unfold birkhoffAverage birkhoffSum
  rw [integral_smul, integral_finsetSum (Finset.range n) (f := fun i ω => f ((T^[i]) ω)) (fun i _ =>
    (hT.iterate i).integrable_comp_of_integrable hi)]
  simp only [hcomp, Finset.sum_const, Finset.card_range, nsmul_eq_mul, smul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)), one_mul]

private theorem average_nonneg {Ω : Type*} (T : Ω → Ω) (f : Ω → ℝ)
    (hf : ∀ ω, 0 ≤ f ω) (n : ℕ) (ω : Ω) :
    0 ≤ birkhoffAverage ℝ T f n ω := by
  unfold birkhoffAverage birkhoffSum
  exact smul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))
    (Finset.sum_nonneg fun i _ => hf _)

private theorem exists_nonneg_l1 {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω} {f : Ω → ℝ}
    (hT : MeasurePreserving T μ μ) (hm : Measurable f) (hi : Integrable f μ)
    (hf : ∀ ω, 0 ≤ f ω) :
    ∃ g : Ω → ℝ, Measurable g ∧ Integrable g μ ∧
      (∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => birkhoffAverage ℝ T f n ω) atTop (𝓝 (g ω))) ∧
      (∀ᵐ ω ∂μ, g (T ω) = g ω) ∧ (∫ ω, g ω ∂μ) = ∫ ω, f ω ∂μ ∧
      Tendsto (fun n : ℕ => ∫ ω, |birkhoffAverage ℝ T f n ω - g ω| ∂μ)
        atTop (𝓝 0) := by
  obtain ⟨g, hgm, hgi, hconv, hinv, hmean⟩ := exists_birkhoffPointwise hT hm hi
  have hgn : ∀ᵐ ω ∂μ, 0 ≤ g ω := by
    filter_upwards [hconv] with ω hω
    exact ge_of_tendsto hω (Eventually.of_forall fun n => average_nonneg T f hf n ω)
  have hmeans : Tendsto (fun n : ℕ => ∫ ω, birkhoffAverage ℝ T f n ω ∂μ)
      atTop (𝓝 (∫ ω, g ω ∂μ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact hmean.trans (integral_birkhoffAverage_of_pos hT hm hi hn).symm
  refine ⟨g, hgm, hgi, hconv, hinv, hmean, ?_⟩
  exact tendsto_integral_abs_sub_of_ae_tendsto (integrable_birkhoffAverage hT hi)
    hgi (fun n => ae_of_all μ (average_nonneg T f hf n)) hgn hconv hmeans

/-- One measurable integrable invariant witness for almost sure and L1
convergence of the actual signed forward averages, preserving the mean.
No ergodicity or invertibility is assumed. -/
theorem exists_birkhoffL1 {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω} {f : Ω → ℝ}
    (hT : MeasurePreserving T μ μ) (hm : Measurable f) (hi : Integrable f μ) :
    ∃ g : Ω → ℝ, Measurable g ∧ Integrable g μ ∧
      (∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => birkhoffAverage ℝ T f n ω) atTop (𝓝 (g ω))) ∧
      (∀ᵐ ω ∂μ, g (T ω) = g ω) ∧ (∫ ω, g ω ∂μ) = ∫ ω, f ω ∂μ ∧
      Tendsto (fun n : ℕ => ∫ ω, |birkhoffAverage ℝ T f n ω - g ω| ∂μ)
        atTop (𝓝 0) := by
  let p : Ω → ℝ := fun ω => max (f ω) 0
  let m : Ω → ℝ := fun ω => max (-f ω) 0
  have hpi : Integrable p μ := hi.pos_part
  have hmi : Integrable m μ := hi.neg.pos_part
  obtain ⟨u, hum, hui, huc, huinv, humean, huL1⟩ :=
    exists_nonneg_l1 (f := p) hT (hm.max measurable_const) hpi (fun ω => le_max_right _ _)
  obtain ⟨v, hvm, hvi, hvc, hvinv, hvmean, hvL1⟩ :=
    exists_nonneg_l1 (f := m) hT (by simpa only [m, Pi.neg_apply] using hm.neg.max measurable_const)
      hmi (fun ω => le_max_right _ _)
  have hsplit : f = p - m := by
    funext ω
    dsimp only [p, m, Pi.sub_apply]
    exact (max_zero_sub_max_neg_zero_eq_self (f ω)).symm
  have havg (n : ℕ) (ω : Ω) : birkhoffAverage ℝ T f n ω =
      birkhoffAverage ℝ T p n ω - birkhoffAverage ℝ T m n ω := by
    rw [hsplit, birkhoffAverage_sub_apply]
  refine ⟨u - v, hum.sub hvm, hui.sub hvi, ?_, ?_, ?_, ?_⟩
  · filter_upwards [huc, hvc] with ω hu hv
    simpa only [havg, Pi.sub_apply] using hu.sub hv
  · filter_upwards [huinv, hvinv] with ω hu hv
    change u (T ω) - v (T ω) = u ω - v ω
    rw [hu, hv]
  · simp only [Pi.sub_apply]
    rw [integral_sub hui hvi, humean, hvmean]
    have hint : (∫ ω, f ω ∂μ) = (∫ ω, p ω ∂μ) - ∫ ω, m ω ∂μ := by
      conv_lhs => rw [hsplit]
      simpa only [Pi.sub_apply] using integral_sub hpi hmi
    exact hint.symm
  · have hbound (n : ℕ) : (∫ ω, |birkhoffAverage ℝ T f n ω - (u - v) ω| ∂μ) ≤
        (∫ ω, |birkhoffAverage ℝ T p n ω - u ω| ∂μ) +
        (∫ ω, |birkhoffAverage ℝ T m n ω - v ω| ∂μ) := by
      have hpabs : Integrable (fun ω => |birkhoffAverage ℝ T p n ω - u ω|) μ := by
        simpa only [Pi.sub_apply] using ((integrable_birkhoffAverage hT hpi n).sub hui).abs
      have hmabs : Integrable (fun ω => |birkhoffAverage ℝ T m n ω - v ω|) μ := by
        simpa only [Pi.sub_apply] using ((integrable_birkhoffAverage hT hmi n).sub hvi).abs
      rw [← integral_add hpabs hmabs]
      apply integral_mono ((integrable_birkhoffAverage hT hi n).sub (hui.sub hvi)).abs
        (((integrable_birkhoffAverage hT hpi n).sub hui).abs.add
          ((integrable_birkhoffAverage hT hmi n).sub hvi).abs)
      intro ω
      simp only [Pi.sub_apply, Pi.add_apply]
      rw [havg]
      have heq : birkhoffAverage ℝ T p n ω - birkhoffAverage ℝ T m n ω - (u ω - v ω) =
          (birkhoffAverage ℝ T p n ω - u ω) - (birkhoffAverage ℝ T m n ω - v ω) := by ring
      rw [heq]
      exact abs_sub _ _
    have hz := huL1.add hvL1
    simp only [add_zero] at hz
    exact squeeze_zero (fun n => integral_nonneg fun ω => abs_nonneg _) hbound hz

end LPPDifferentiability
