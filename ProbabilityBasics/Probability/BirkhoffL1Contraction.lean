/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.BirkhoffL1
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Integral contraction for the actual finite Birkhoff averages. -/

public section

open MeasureTheory

namespace ProbabilityBasics

/-- Averaging two integrable observables under one measure-preserving map does not
increase their integral absolute difference. This is the norm-iteration input to
the invariant-set identification route of Krengel, *Ergodic Theorems*,
§6.2.8 remark, p. 206. -/
theorem integral_abs_birkhoffAverage_sub_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (f g : Ω → ℝ) (hf : Integrable f μ) (hg : Integrable g μ) (n : ℕ) :
    (∫ s, |birkhoffAverage ℝ T f n s - birkhoffAverage ℝ T g n s| ∂μ) ≤
      ∫ s, |f s - g s| ∂μ := by
  let q : Ω → ℝ := fun s => |f s - g s|
  have hq : Integrable q μ := by
    simpa only [Pi.sub_apply, q] using (hf.sub hg).abs
  have hiterateIntegrable (i : ℕ) : Integrable (fun s => q ((T^[i]) s)) μ := by
    exact (hT.iterate i).integrable_comp_of_integrable hq
  have hiterateIntegral (i : ℕ) :
      (∫ s, q ((T^[i]) s) ∂μ) = ∫ s, q s ∂μ := by
    have hTi : MeasurePreserving (T^[i]) μ μ := hT.iterate i
    have hqMap : AEStronglyMeasurable q (Measure.map (T^[i]) μ) := by
      rw [hTi.map_eq]
      exact hq.aestronglyMeasurable
    have hmap := integral_map hTi.measurable.aemeasurable hqMap
    rw [hTi.map_eq] at hmap
    exact hmap.symm
  by_cases hn : n = 0
  · subst n
    simp only [birkhoffAverage_zero, sub_self, abs_zero, integral_zero]
    exact integral_nonneg fun s => abs_nonneg (f s - g s)
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hpointwise (s : Ω) :
        |birkhoffAverage ℝ T f n s - birkhoffAverage ℝ T g n s| ≤
          (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, q ((T^[i]) s) := by
      rw [← birkhoffAverage_sub_apply]
      simp only [birkhoffAverage, birkhoffSum, smul_eq_mul, Pi.sub_apply, q]
      calc
        |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
            (f ((T^[i]) s) - g ((T^[i]) s))| =
            |(n : ℝ)⁻¹| *
              |∑ i ∈ Finset.range n, (f ((T^[i]) s) - g ((T^[i]) s))| := abs_mul _ _
        _ = (n : ℝ)⁻¹ *
              |∑ i ∈ Finset.range n, (f ((T^[i]) s) - g ((T^[i]) s))| := by
          rw [abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))]
        _ ≤ (n : ℝ)⁻¹ *
              ∑ i ∈ Finset.range n,
                |f ((T^[i]) s) - g ((T^[i]) s)| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
            (inv_nonneg.mpr (Nat.cast_nonneg n))
        _ = (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, q ((T^[i]) s) := rfl
    have hleft : Integrable
        (fun s => |birkhoffAverage ℝ T f n s - birkhoffAverage ℝ T g n s|) μ := by
      simpa only [Pi.sub_apply] using
        ((LPPDifferentiability.integrable_birkhoffAverage hT hf n).sub
          (LPPDifferentiability.integrable_birkhoffAverage hT hg n)).abs
    have hright : Integrable
        (fun s => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, q ((T^[i]) s)) μ := by
      have hsum := integrable_finsetSum (Finset.range n)
        (fun i _ => hiterateIntegrable i)
      simpa only [smul_eq_mul] using hsum.const_mul (n : ℝ)⁻¹
    have hintegral_smul :
        (∫ s, (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, q ((T^[i]) s) ∂μ) =
          ∫ s, q s ∂μ := by
      rw [integral_smul,
        integral_finsetSum (Finset.range n) (fun i _ => hiterateIntegrable i)]
      simp_rw [hiterateIntegral]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, smul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hnpos)), one_mul]
    have hintegral :
        (∫ s, (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, q ((T^[i]) s) ∂μ) =
          ∫ s, q s ∂μ := by
      simpa only [smul_eq_mul] using hintegral_smul
    calc
      (∫ s, |birkhoffAverage ℝ T f n s - birkhoffAverage ℝ T g n s| ∂μ) ≤
          ∫ s, (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, q ((T^[i]) s) ∂μ :=
        integral_mono hleft hright hpointwise
      _ = ∫ s, |f s - g s| ∂μ := by simpa only [q] using hintegral

end ProbabilityBasics
