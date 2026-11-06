/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.OppositeMonotoneIntegral
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Product integrals of oppositely monotone functions

A bounded jointly measurable family of increasing functions can be averaged
over a probability space and compared with an integrable decreasing function
under another probability measure.
-/

public section

open MeasureTheory

namespace LPPDifferentiability

/-- The scalar opposite-monotonicity inequality remains valid on a genuine
product probability space when the increasing factor depends measurably on a
second coordinate. -/
theorem integrable_and_integral_mul_le_mul_integrals_of_monotone_antitone_prod
    {β : Type*} [MeasurableSpace β]
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {ν : Measure β} [IsProbabilityMeasure ν]
    {f : ℝ × β → ℝ} {W : ℝ → ℝ}
    (hf : Measurable f)
    (hf_nonneg : ∀ x b, 0 ≤ f (x, b))
    (hf_le_one : ∀ x b, f (x, b) ≤ 1)
    (hf_mono : ∀ b, Monotone fun x => f (x, b))
    (hW : Antitone W) (hW_int : Integrable W μ) :
    Integrable f (μ.prod ν) ∧
      Integrable (fun p => f p * W p.1) (μ.prod ν) ∧
      (∫ p, f p * W p.1 ∂μ.prod ν) ≤
        (∫ p, f p ∂μ.prod ν) * (∫ x, W x ∂μ) := by
  let g : ℝ → ℝ := fun x => ∫ b, f (x, b) ∂ν

  have hf_section_meas (x : ℝ) : Measurable fun b => f (x, b) :=
    hf.comp measurable_prodMk_left
  have hf_section_bound (x : ℝ) : ∀ᵐ b ∂ν, ‖f (x, b)‖ ≤ 1 := by
    filter_upwards with b
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hf_nonneg x b)] using hf_le_one x b
  have hf_section_int (x : ℝ) : Integrable (fun b => f (x, b)) ν :=
    Integrable.of_bound (hf_section_meas x).aestronglyMeasurable 1 (hf_section_bound x)

  have hg_mono : Monotone g := by
    intro x y hxy
    dsimp only [g]
    exact integral_mono (hf_section_int x) (hf_section_int y) fun b => hf_mono b hxy
  have hg_nonneg (x : ℝ) : 0 ≤ g x := by
    dsimp only [g]
    exact integral_nonneg_of_ae (ae_of_all ν fun b => hf_nonneg x b)
  have hg_le_one (x : ℝ) : g x ≤ 1 := by
    dsimp only [g]
    calc
      (∫ b, f (x, b) ∂ν) ≤ ∫ b, (1 : ℝ) ∂ν :=
        integral_mono (hf_section_int x) (integrable_const 1) fun b => hf_le_one x b
      _ = 1 := by simp [probReal_univ]

  have hcov :=
    integrable_and_integral_mul_le_mul_integrals_of_monotone_antitone
      hg_mono hg_nonneg hg_le_one hW hW_int
  rcases hcov with ⟨hg_int, hgw_int, hcov⟩

  have hprod_bound : ∀ᵐ p ∂μ.prod ν, ‖f p‖ ≤ 1 := by
    filter_upwards with p
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hf_nonneg p.1 p.2)] using
      hf_le_one p.1 p.2
  have hf_prod_int : Integrable f (μ.prod ν) :=
    Integrable.of_bound hf.aestronglyMeasurable 1 hprod_bound
  have hW_fst_int : Integrable (fun p : ℝ × β => W p.1) (μ.prod ν) :=
    hW_int.comp_fst ν
  have hfw_prod_int : Integrable (fun p : ℝ × β => f p * W p.1) (μ.prod ν) := by
    have hmul_int : Integrable (f * fun p : ℝ × β => W p.1) (μ.prod ν) := by
      simpa only [smul_eq_mul] using
        hW_fst_int.bdd_smul 1 hf.aestronglyMeasurable hprod_bound
    exact hmul_int.congr <| ae_of_all (μ.prod ν) fun p => by
      simp only [Pi.mul_apply]

  have hf_fubini :
      (∫ p, f p ∂μ.prod ν) = ∫ x, g x ∂μ := by
    calc
      (∫ p, f p ∂μ.prod ν) = ∫ x, ∫ b, f (x, b) ∂ν ∂μ :=
        integral_prod f hf_prod_int
      _ = ∫ x, g x ∂μ := by rfl

  have hfw_fubini :
      (∫ p, f p * W p.1 ∂μ.prod ν) = ∫ x, g x * W x ∂μ := by
    calc
      (∫ p, f p * W p.1 ∂μ.prod ν) =
          ∫ x, ∫ b, f (x, b) * W x ∂ν ∂μ :=
        integral_prod (fun p : ℝ × β => f p * W p.1) hfw_prod_int
      _ = ∫ x, (∫ b, f (x, b) ∂ν) * W x ∂μ := by
        apply integral_congr_ae
        exact ae_of_all μ fun x => integral_mul_const_of_integrable (hf_section_int x)
      _ = ∫ x, g x * W x ∂μ := by rfl

  refine ⟨hf_prod_int, hfw_prod_int, ?_⟩
  calc
    (∫ p, f p * W p.1 ∂μ.prod ν) = ∫ x, g x * W x ∂μ := hfw_fubini
    _ ≤ (∫ x, g x ∂μ) * (∫ x, W x ∂μ) := hcov
    _ = (∫ p, f p ∂μ.prod ν) * (∫ x, W x ∂μ) := by rw [← hf_fubini]

end LPPDifferentiability
