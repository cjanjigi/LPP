/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# First-moment control of the negative truncation remainder

For an integrable real weight, its negative truncation remainder is integrable
for each nonnegative cutoff, and its mean tends to zero as the cutoff tends to
positive infinity.
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace LPPDifferentiability

private theorem negative_remainder_mean_nonneg (L x : ℝ) :
    0 ≤ max (-L - x) 0 :=
  le_max_right _ _

private theorem negative_remainder_le_abs_of_nonneg_cutoff
    (L x : ℝ) (hL : 0 ≤ L) : max (-L - x) 0 ≤ |x| := by
  calc
    max (-L - x) 0 ≤ max (-x) 0 :=
      max_le_max
        (by simpa only [zero_sub] using sub_le_sub_right (neg_nonpos.mpr hL) x)
        le_rfl
    _ ≤ |x| := by
      by_cases hx : 0 ≤ x
      · rw [max_eq_right (neg_nonpos.mpr hx), abs_of_nonneg hx]
        exact hx
      · have hx' : x < 0 := lt_of_not_ge hx
        rw [max_eq_left (neg_nonneg.mpr hx'.le), abs_of_neg hx']

private theorem integrable_negative_remainder_mean_of_integrable_id {μ : Measure ℝ}
    (hμ : Integrable id μ) (L : ℝ) (hL : 0 ≤ L) :
    Integrable (fun x : ℝ => max (-L - x) 0) μ := by
  have h_abs : Integrable (fun x : ℝ => |x|) μ := by
    simpa using hμ.abs
  have h_cont : Continuous (fun x : ℝ => max (-L - x) 0) :=
    (continuous_const.sub continuous_id).max continuous_const
  refine h_abs.mono' h_cont.aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (negative_remainder_mean_nonneg L x)]
  exact negative_remainder_le_abs_of_nonneg_cutoff L x hL

/-- The mean negative truncation remainder tends to zero at positive infinity. -/
theorem tendsto_integral_negative_remainder_zero {μ : Measure ℝ}
    (hμ : Integrable id μ) :
    Tendsto (fun L : ℝ => ∫ x, max (-L - x) 0 ∂μ) atTop (𝓝 0) := by
  have h_abs : Integrable (fun x : ℝ => |x|) μ := by
    simpa using hμ.abs
  have h_meas : ∀ᶠ L : ℝ in atTop,
      AEStronglyMeasurable (fun x : ℝ => max (-L - x) 0) μ := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
    exact (integrable_negative_remainder_mean_of_integrable_id hμ L hL).aestronglyMeasurable
  have h_bound : ∀ᶠ L : ℝ in atTop, ∀ᵐ x ∂μ,
      ‖max (-L - x) 0‖ ≤ |x| := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (negative_remainder_mean_nonneg L x)]
    exact negative_remainder_le_abs_of_nonneg_cutoff L x hL
  have h_pointwise (x : ℝ) :
      Tendsto (fun L : ℝ => max (-L - x) 0) atTop (𝓝 0) := by
    apply tendsto_nhds_of_eventually_eq
    refine eventually_atTop.2 ⟨-x, ?_⟩
    intro L hL
    have hneg : -L ≤ x := by
      simpa only [neg_neg] using neg_le_neg hL
    have hzero : -L - x ≤ 0 := sub_nonpos.mpr hneg
    simp only [max_eq_right hzero]
  have h_lim : ∀ᵐ x ∂μ,
      Tendsto (fun L : ℝ => max (-L - x) 0) atTop (𝓝 0) :=
    ae_of_all μ h_pointwise
  have h_integrals :=
    tendsto_integral_filter_of_dominated_convergence
      (bound := fun x : ℝ => |x|)
      (F := fun L x => max (-L - x) 0)
      (f := fun _ : ℝ => (0 : ℝ))
      (l := atTop)
      h_meas h_bound h_abs h_lim
  simpa using h_integrals

end LPPDifferentiability
