/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.UniformOriginIncrements
public import Mathlib.Probability.IdentDistrib

/-!
# Positive-part bounds for uniform-origin increments

These lemmas take the one-step inputs as hypotheses, and implement equation (2.10)
of Liggett (1985). The array must later supply the one-step domination and the
common one-step law.
-/

public section

open MeasureTheory ProbabilityTheory

namespace LPPDifferentiability

/-- Countably many inequalities lift through the first projection. -/
theorem uniformOriginIncrement_le_ae {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X Z : ℕ → Ω → ℝ)
    (h : ∀ j, 0 < j → ∀ᵐ ω ∂μ, X (j + 1) ω - X j ω ≤ Z j ω) (n k : ℕ) :
    ∀ᵐ p ∂uniformOriginProduct μ n,
      uniformOriginIncrement X n k p ≤ Z (k + p.2.val + 1) p.1 := by
  have hall : ∀ᵐ ω ∂μ, ∀ j, 0 < j → X (j + 1) ω - X j ω ≤ Z j ω := by
    rw [ae_all_iff]
    intro j
    by_cases hj : 0 < j
    · filter_upwards [h j hj] with ω hω using fun _ => hω
    · exact ae_of_all _ (fun _ hj' => (hj hj').elim)
  filter_upwards [(uniformOriginProduct_fst μ n).quasiMeasurePreserving.ae hall] with p hp
  exact hp (k + p.2.val + 1) (by omega)

/-- A monotone transformed increment is bounded by the common-law expectation.
The finite average uses the uniform product integration theorem. -/
theorem integral_uniformOriginIncrement_comp_le {Ω A : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure A)
    (X Z : ℕ → Ω → ℝ) (g : A → ℝ)
    (hdom : ∀ j, 0 < j → ∀ᵐ ω ∂μ, X (j + 1) ω - X j ω ≤ Z j ω)
    (hlaw : ∀ j, 0 < j → IdentDistrib (Z j) g μ ν)
    (φ : ℝ → ℝ) (hφ : Measurable φ) (hmono : Monotone φ)
    (hg : Integrable (fun a => φ (g a)) ν)
    (hm : ∀ j, 0 < j → Measurable (X j))
    (hi : ∀ j, 0 < j → Integrable (fun ω => φ (X (j + 1) ω - X j ω)) μ)
    (n k : ℕ) :
    (∫ p, φ (uniformOriginIncrement X n k p) ∂uniformOriginProduct μ n) ≤
      ∫ a, φ (g a) ∂ν := by
  rw [show (fun p => φ (uniformOriginIncrement X n k p)) =
      (fun p : Ω × Fin (n + 1) => φ (X (k + p.2.val + 2) p.1 -
        X (k + p.2.val + 1) p.1)) from rfl]
  rw [integral_uniformOrigin_family μ n
    (fun u ω => φ (X (k + u.val + 2) ω - X (k + u.val + 1) ω))
    (fun u => hφ.comp ((hm _ (by omega)).sub (hm _ (by omega))))
    (fun u => hi (k + u.val + 1) (by omega))]
  have hcoord (u : Fin (n + 1)) :
      (∫ ω, φ (X (k + u.val + 2) ω - X (k + u.val + 1) ω) ∂μ) ≤
        ∫ a, φ (g a) ∂ν := by
    have hd := (hlaw (k + u.val + 1) (by omega)).comp hφ
    have heq : (∫ ω, φ (Z (k + u.val + 1) ω) ∂μ) =
        ∫ a, φ (g a) ∂ν := hd.integral_eq
    rw [← heq]
    apply integral_mono_ae (hi _ (by omega)) (hd.integrable_iff.mpr hg)
    filter_upwards [hdom (k + u.val + 1) (by omega)] with ω hω
    exact hmono hω
  calc
    _ ≤ (∑ _u : Fin (n + 1), ∫ a, φ (g a) ∂ν) / (n + 1 : ℝ) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun u _ => hcoord u)) (by positivity)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      simp only [Nat.cast_add, Nat.cast_one]
      exact mul_div_cancel_left₀ _ (show (n + 1 : ℝ) ≠ 0 by positivity)

/-- Equation (2.10) of Liggett (1985), with no value of `X 0` used. -/
theorem integral_uniformOriginIncrement_pos_le {Ω A : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure A)
    (X Z : ℕ → Ω → ℝ) (g : A → ℝ)
    (hdom : ∀ j, 0 < j → ∀ᵐ ω ∂μ, X (j + 1) ω - X j ω ≤ Z j ω)
    (hlaw : ∀ j, 0 < j → IdentDistrib (Z j) g μ ν)
    (hg : Integrable g ν) (hm : ∀ j, 0 < j → Measurable (X j))
    (hi : ∀ j, 0 < j → Integrable (X j) μ) (n k : ℕ) :
    (∫ p, max (uniformOriginIncrement X n k p) 0 ∂uniformOriginProduct μ n) ≤
      ∫ a, max (g a) 0 ∂ν := by
  apply integral_uniformOriginIncrement_comp_le μ ν X Z g hdom hlaw
    (fun x => max x 0) (measurable_id.max measurable_const)
    (fun _ _ h => max_le_max h le_rfl) (hg.sup (integrable_zero _ _ _)) hm
  intro j hj
  exact ((hi (j + 1) (by omega)).sub (hi j hj)).sup (integrable_zero _ _ _)

end LPPDifferentiability
