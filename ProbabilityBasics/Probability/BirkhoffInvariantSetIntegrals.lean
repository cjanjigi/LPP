/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProbabilityBasics.Probability.BirkhoffL1
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Dynamics.BirkhoffSum.QuasiMeasurePreserving

/-! One Birkhoff L¹ limit preserves the integral on every strictly invariant measurable set. -/

@[expose] public section

open MeasureTheory Filter
open scoped Topology BigOperators

namespace ProbabilityBasics

private theorem setIntegral_birkhoffAverage_of_pos
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (f : Ω → ℝ) (hf : Integrable f μ)
    (A : Set Ω) (hA : MeasurableSet A) (hInv : T ⁻¹' A = A)
    {n : ℕ} (hn : 0 < n) :
    (∫ s in A, birkhoffAverage ℝ T f n s ∂μ) = ∫ s in A, f s ∂μ := by
  -- Strict set invariance propagates through every actual iterate.
  have hIterInv (k : ℕ) : (T^[k]) ⁻¹' A = A := by
    induction k with
    | zero => simp only [Function.iterate_zero, Set.preimage_id]
    | succ k hk => rw [Function.iterate_succ, Set.preimage_comp, hk, hInv]
  have hIterMean (k : ℕ) : (∫ s in A, f ((T^[k]) s) ∂μ) = ∫ s in A, f s ∂μ := by
    have hMapped : AEStronglyMeasurable f (μ.map (T^[k])) := by
      rw [(hT.iterate k).map_eq]
      exact hf.aestronglyMeasurable
    have hMap := setIntegral_map (μ := μ) (g := T^[k]) (f := f) hA hMapped
      (hT.iterate k).aemeasurable
    rw [(hT.iterate k).map_eq, hIterInv k] at hMap
    exact hMap.symm
  -- Every summand is genuinely integrable on the restricted law; no probability is needed there.
  unfold birkhoffAverage birkhoffSum
  rw [integral_smul, integral_finsetSum (Finset.range n)
    (f := fun k s => f ((T^[k]) s)) (fun k _ =>
      ((hT.iterate k).integrable_comp_of_integrable hf).restrict)]
  simp only [hIterMean, Finset.sum_const, Finset.card_range, nsmul_eq_mul, smul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)), one_mul]

private theorem abs_setIntegral_sub_le_integral_abs
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (A : Set Ω)
    (u v : Ω → ℝ) (hu : Integrable u μ) (hv : Integrable v μ) :
    |(∫ s in A, u s ∂μ) - ∫ s in A, v s ∂μ| ≤ ∫ s, |u s - v s| ∂μ := by
  have hAbs : Integrable (fun s => |u s - v s|) μ := by
    simpa only [Pi.sub_apply] using (hu.sub hv).abs
  calc
    |(∫ s in A, u s ∂μ) - ∫ s in A, v s ∂μ| = |∫ s in A, u s - v s ∂μ| := by
      rw [integral_sub hu.restrict hv.restrict]
    _ ≤ ∫ s in A, |u s - v s| ∂μ := by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (μ := μ.restrict A) (fun s => u s - v s))
    _ ≤ ∫ s, |u s - v s| ∂μ :=
      setIntegral_le_integral hAbs (Eventually.of_forall fun s => abs_nonneg (u s - v s))

/-- An integrable real observable has one measurable integrable Birkhoff L¹ limit
that preserves its integral on every measurable strictly invariant set. This is
Krengel, Ergodic Theorems, §6.2 Theorem 2.8, finite-measure identification remark, p.206.
The original observable need only be integrable; no ergodicity is assumed. -/
theorem exists_birkhoffL1_invariant_set_integrals
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (f : Ω → ℝ) (hf : Integrable f μ) :
    ∃ g : Ω → ℝ, Measurable g ∧ Integrable g μ ∧
      (∀ᵐ s ∂μ, g (T s) = g s) ∧
      Tendsto (fun n : ℕ => ∫ s, |birkhoffAverage ℝ T f n s - g s| ∂μ)
        atTop (𝓝 0) ∧
      (∀ A : Set Ω, MeasurableSet A → T ⁻¹' A = A →
        (∫ s in A, g s ∂μ) = ∫ s in A, f s ∂μ) := by
  -- The existing producer receives a measurable version of the original L¹ input.
  let f' : Ω → ℝ := hf.aestronglyMeasurable.mk f
  have hMeas : Measurable f' := hf.aestronglyMeasurable.measurable_mk
  have hEq : f =ᵐ[μ] f' := hf.aestronglyMeasurable.ae_eq_mk
  have hInt : Integrable f' μ := hf.congr hEq
  obtain ⟨g, hgm, hgi, _, hginv, _, hL1Version⟩ :=
    LPPDifferentiability.exists_birkhoffL1 hT hMeas hInt
  -- Quasi-preservation transfers the actual finite averages, keeping this SAME g.
  have hErrorEq (n : ℕ) :
      (∫ s, |birkhoffAverage ℝ T f n s - g s| ∂μ) =
        ∫ s, |birkhoffAverage ℝ T f' n s - g s| ∂μ := by
    apply integral_congr_ae
    filter_upwards [hT.quasiMeasurePreserving.birkhoffAverage_ae_eq_of_ae_eq ℝ hEq n] with s hs
    rw [hs]
  have hL1 : Tendsto (fun n : ℕ => ∫ s, |birkhoffAverage ℝ T f n s - g s| ∂μ)
      atTop (𝓝 0) :=
    hL1Version.congr' (Eventually.of_forall fun n => (hErrorEq n).symm)
  refine ⟨g, hgm, hgi, hginv, hL1, ?_⟩
  intro A hA hInv
  -- Restricted integral errors are bounded by the whole original-average L¹ error.
  have hBound (n : ℕ) :
      |(∫ s in A, birkhoffAverage ℝ T f n s ∂μ) - ∫ s in A, g s ∂μ| ≤
        ∫ s, |birkhoffAverage ℝ T f n s - g s| ∂μ :=
    abs_setIntegral_sub_le_integral_abs μ A (birkhoffAverage ℝ T f n) g
      (LPPDifferentiability.integrable_birkhoffAverage hT hf n) hgi
  have hErrorLimit : Tendsto (fun n : ℕ =>
      |(∫ s in A, birkhoffAverage ℝ T f n s ∂μ) - ∫ s in A, g s ∂μ|)
      atTop (𝓝 0) :=
    squeeze_zero (fun n => abs_nonneg _) hBound hL1
  have hConstantLimit : Tendsto (fun _ : ℕ =>
      |(∫ s in A, f s ∂μ) - ∫ s in A, g s ∂μ|) atTop (𝓝 0) := by
    apply hErrorLimit.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [setIntegral_birkhoffAverage_of_pos μ T hT f hf A hA hInv hn]
  have hZero : |(∫ s in A, f s ∂μ) - ∫ s in A, g s ∂μ| = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hConstantLimit
  exact (sub_eq_zero.mp (abs_eq_zero.mp hZero)).symm

end ProbabilityBasics
