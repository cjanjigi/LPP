/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integrals of oppositely monotone functions

A bounded increasing function and an integrable decreasing function have
nonpositive covariance under a probability measure. The proof uses two
coordinates with the product measure; it needs no second moment or
atom-free assumption.
-/

public section

open MeasureTheory

namespace LPPDifferentiability

/-- A bounded nondecreasing function and an integrable nonincreasing function
have nonpositive covariance under a probability measure. The first two
conclusions record the integrability needed for the inequality. -/
theorem integrable_and_integral_mul_le_mul_integrals_of_monotone_antitone
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {f W : ℝ → ℝ}
    (hf : Monotone f) (hf_nonneg : ∀ x, 0 ≤ f x) (hf_le_one : ∀ x, f x ≤ 1)
    (hW : Antitone W) (hW_int : Integrable W μ) :
    Integrable f μ ∧ Integrable (f * W) μ ∧
      (∫ x, f x * W x ∂μ) ≤ (∫ x, f x ∂μ) * (∫ x, W x ∂μ) := by
  have hf_meas : Measurable f := hf.measurable
  have hf_bound : ∀ᵐ x ∂μ, ‖f x‖ ≤ 1 := by
    filter_upwards with x
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hf_nonneg x)] using hf_le_one x
  have hf_int : Integrable f μ :=
    Integrable.of_bound hf_meas.aestronglyMeasurable 1 hf_bound
  have hfw_int : Integrable (f * W) μ := by
    simpa only [smul_eq_mul] using
      hW_int.bdd_smul 1 hf_meas.aestronglyMeasurable hf_bound

  let a₁₁ : ℝ × ℝ → ℝ := fun p => (f * W) p.1
  let a₁₂ : ℝ × ℝ → ℝ := fun p => f p.1 * W p.2
  let a₂₁ : ℝ × ℝ → ℝ := fun p => f p.2 * W p.1
  let a₂₂ : ℝ × ℝ → ℝ := fun p => (f * W) p.2
  have ha₁₁ : Integrable a₁₁ (μ.prod μ) := hfw_int.comp_fst μ
  have ha₁₂ : Integrable a₁₂ (μ.prod μ) := hf_int.mul_prod hW_int
  have ha₂₁ : Integrable a₂₁ (μ.prod μ) := by
    simpa only [mul_comm] using hW_int.mul_prod hf_int
  have ha₂₂ : Integrable a₂₂ (μ.prod μ) := hfw_int.comp_snd μ
  let g : ℝ × ℝ → ℝ := fun p => (f p.1 - f p.2) * (W p.1 - W p.2)
  have hg_eq : g = (a₁₁ - a₁₂) - (a₂₁ - a₂₂) := by
    funext p
    simp only [g, a₁₁, a₁₂, a₂₁, a₂₂, Pi.mul_apply, Pi.sub_apply]
    ring
  have hg_int : Integrable g (μ.prod μ) := by
    rw [hg_eq]
    exact (ha₁₁.sub ha₁₂).sub (ha₂₁.sub ha₂₂)
  have hg_nonpos : ∀ p, g p ≤ 0 := by
    intro p
    dsimp [g]
    rcases le_total p.1 p.2 with hxy | hyx
    · exact mul_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr (hf hxy)) (sub_nonneg.mpr (hW hxy))
    · exact mul_nonpos_of_nonneg_of_nonpos
        (sub_nonneg.mpr (hf hyx)) (sub_nonpos.mpr (hW hyx))
  have hg_integral_nonpos : (∫ p, g p ∂μ.prod μ) ≤ 0 := by
    have hzero : Integrable (fun _ : ℝ × ℝ => (0 : ℝ)) (μ.prod μ) :=
      (integrable_zero (ℝ × ℝ) ℝ (μ.prod μ)).congr (ae_of_all _ fun _ => rfl)
    calc
      (∫ p, g p ∂μ.prod μ) ≤ ∫ p, (0 : ℝ) ∂μ.prod μ :=
        integral_mono hg_int hzero hg_nonpos
      _ = 0 := by simp

  have ha₁₁_integral :
      (∫ p, a₁₁ p ∂μ.prod μ) = ∫ x, f x * W x ∂μ := by
    calc
      (∫ p, a₁₁ p ∂μ.prod μ) = μ.real Set.univ • ∫ x, f x * W x ∂μ := by
        change (∫ p, (f * W) p.1 ∂μ.prod μ) = _
        simpa only [Pi.mul_apply] using
          (integral_fun_fst (μ := μ) (ν := μ) (f * W))
      _ = _ := by simp only [probReal_univ, one_smul]
  have ha₁₂_integral :
      (∫ p, a₁₂ p ∂μ.prod μ) =
        (∫ x, f x ∂μ) * (∫ x, W x ∂μ) := by
    change (∫ p, f p.1 * W p.2 ∂μ.prod μ) = _
    exact integral_prod_mul f W
  have ha₂₁_integral :
      (∫ p, a₂₁ p ∂μ.prod μ) =
        (∫ x, f x ∂μ) * (∫ x, W x ∂μ) := by
    calc
      (∫ p, a₂₁ p ∂μ.prod μ) = ∫ p, W p.1 * f p.2 ∂μ.prod μ := by
        apply integral_congr_ae
        exact ae_of_all _ fun p => mul_comm _ _
      _ = (∫ x, W x ∂μ) * (∫ x, f x ∂μ) := integral_prod_mul W f
      _ = _ := mul_comm _ _
  have ha₁₁_sub_ha₁₂_integral :
      (∫ p, (a₁₁ - a₁₂) p ∂μ.prod μ) =
        (∫ p, a₁₁ p ∂μ.prod μ) - (∫ p, a₁₂ p ∂μ.prod μ) := by
    simpa only [Pi.sub_apply] using (integral_sub ha₁₁ ha₁₂)
  have ha₂₁_sub_ha₂₂_integral :
      (∫ p, (a₂₁ - a₂₂) p ∂μ.prod μ) =
        (∫ p, a₂₁ p ∂μ.prod μ) - (∫ p, a₂₂ p ∂μ.prod μ) := by
    simpa only [Pi.sub_apply] using (integral_sub ha₂₁ ha₂₂)
  have ha₂₂_integral :
      (∫ p, a₂₂ p ∂μ.prod μ) = ∫ x, f x * W x ∂μ := by
    calc
      (∫ p, a₂₂ p ∂μ.prod μ) = μ.real Set.univ • ∫ x, f x * W x ∂μ := by
        change (∫ p, (f * W) p.2 ∂μ.prod μ) = _
        simpa only [Pi.mul_apply] using
          (integral_fun_snd (μ := μ) (ν := μ) (f * W))
      _ = _ := by simp only [probReal_univ, one_smul]
  have hg_integral_expansion :
      (∫ p, g p ∂μ.prod μ) =
        (∫ x, f x * W x ∂μ) - (∫ x, f x ∂μ) * (∫ x, W x ∂μ) -
          (∫ x, f x ∂μ) * (∫ x, W x ∂μ) + (∫ x, f x * W x ∂μ) := by
    calc
      (∫ p, g p ∂μ.prod μ) =
          ∫ p, (a₁₁ p - a₁₂ p) - (a₂₁ p - a₂₂ p) ∂μ.prod μ := by
        apply integral_congr_ae
        exact ae_of_all _ fun p => congrFun hg_eq p
      _ = (∫ p, (a₁₁ - a₁₂) p ∂μ.prod μ) -
          (∫ p, (a₂₁ - a₂₂) p ∂μ.prod μ) := by
        simpa only [Pi.sub_apply] using
          (integral_sub (ha₁₁.sub ha₁₂) (ha₂₁.sub ha₂₂))
      _ = (∫ p, a₁₁ p ∂μ.prod μ) - (∫ p, a₁₂ p ∂μ.prod μ) -
          ((∫ p, a₂₁ p ∂μ.prod μ) - (∫ p, a₂₂ p ∂μ.prod μ)) := by
        rw [ha₁₁_sub_ha₁₂_integral, ha₂₁_sub_ha₂₂_integral]
      _ = _ := by
        rw [ha₁₁_integral, ha₁₂_integral, ha₂₁_integral, ha₂₂_integral]
        ring
  have hscaled :
      (2 : ℝ) *
        ((∫ x, f x * W x ∂μ) - (∫ x, f x ∂μ) * (∫ x, W x ∂μ)) ≤ 0 := by
    calc
      _ = ∫ p, g p ∂μ.prod μ := by rw [hg_integral_expansion]; ring
      _ ≤ 0 := hg_integral_nonpos
  have hscaled' :
      (2 : ℝ) *
        ((∫ x, f x * W x ∂μ) - (∫ x, f x ∂μ) * (∫ x, W x ∂μ)) ≤ 2 * 0 := by
    simpa using hscaled
  have hdiff :
      (∫ x, f x * W x ∂μ) - (∫ x, f x ∂μ) * (∫ x, W x ∂μ) ≤ 0 :=
    le_of_mul_le_mul_left hscaled' (by norm_num)
  exact ⟨hf_int, hfw_int, sub_nonpos.mp hdiff⟩

end LPPDifferentiability
