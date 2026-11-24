/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! The exact threshold for the two powers in the upper-tail remark. -/

public section

open Filter
open scoped Topology

namespace LPPDifferentiability

/-- Along any sequence of diverging transverse scales, the displayed excess
bound in subsection `sub:ub_mom-chat`, divided by stage count times transverse scale,
tends to zero exactly when `p > 1 + γ`. Stage counts are eventually positive. -/
theorem excess_bound_ratio_tendsto_zero_iff {ι : Type*} (l : Filter ι) [NeBot l]
    (s N : ι → ℝ) (hs : Tendsto s l atTop) (hN : ∀ᶠ i in l, 0 < N i)
    (γ p C : ℝ) (hp : 0 < p) (hC : 0 < C) :
    Tendsto (fun i => C * N i * (s i ^ ((1 + γ) / p) + s i ^ (2 + γ - p)) /
        (N i * s i)) l (𝓝 0) ↔ 1 + γ < p := by
  -- Cancel the stage count and divide each power by the scale.
  have heq : (fun i => C * N i * (s i ^ ((1 + γ) / p) + s i ^ (2 + γ - p)) /
      (N i * s i)) =ᶠ[l]
      fun i => C * (s i ^ ((1 + γ) / p - 1) + s i ^ (1 + γ - p)) := by
    filter_upwards [hs.eventually (eventually_gt_atTop (0 : ℝ)), hN] with i hi hiN
    have hcancel (u : ℝ) : C * N i * u / (N i * s i) = C * (u / s i) := by
      field_simp [hi.ne', hiN.ne']
    have hdiv (b : ℝ) : s i ^ b / s i = s i ^ (b - 1) := by
      rw [Real.rpow_sub hi, Real.rpow_one]
    rw [hcancel, add_div, hdiv, hdiv]
    rw [show 2 + γ - p - 1 = 1 + γ - p by ring]
  rw [tendsto_congr' heq]
  constructor
  · intro h
    by_contra! hnot
    have hsmall : ∀ᶠ i in l, C *
        (s i ^ ((1 + γ) / p - 1) + s i ^ (1 + γ - p)) < C :=
      (tendsto_order.mp h).2 C hC
    have himpossible : ∀ᶠ _i in l, False := by
      filter_upwards [hsmall, hs.eventually (eventually_ge_atTop (1 : ℝ))] with i hi hi1
      -- The second power is at least one when its exponent is nonnegative.
      have hpower : (1 : ℝ) ≤ s i ^ (1 + γ - p) := by
        simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hi1
          (show 0 ≤ 1 + γ - p by linarith only [hnot])
      have hother := Real.rpow_nonneg (zero_le_one.trans hi1) ((1 + γ) / p - 1)
      have hlower : C ≤ C * (s i ^ ((1 + γ) / p - 1) + s i ^ (1 + γ - p)) := by
        calc
          C = C * 1 := (mul_one C).symm
          _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [hpower, hother]) hC.le
      exact (not_lt_of_ge hlower) hi
    obtain ⟨_, hf⟩ := himpossible.exists
    exact hf
  · intro h
    -- Both powers have strictly negative exponents.
    have ha : (1 + γ) / p < 1 := by simpa only [div_lt_iff₀ hp, one_mul] using h
    have h1 := tendsto_rpow_neg_atTop (show 0 < 1 - (1 + γ) / p by linarith only [ha])
    have h2 := tendsto_rpow_neg_atTop (show 0 < p - (1 + γ) by linarith only [h])
    rw [show -(1 - (1 + γ) / p) = (1 + γ) / p - 1 by ring] at h1
    rw [show -(p - (1 + γ)) = 1 + γ - p by ring] at h2
    simpa only [Function.comp_apply, add_zero, mul_zero] using ((h1.comp hs).add (h2.comp hs)).const_mul C

/-- The actual two-power envelope in subsection `sub:ub_mom-chat` is little-o of stage count
times transverse scale exactly when the moment order exceeds `1 + γ`. -/
theorem excess_bound_isLittleO_iff {ι : Type*} (l : Filter ι) [NeBot l]
    (s N : ι → ℝ) (hs : Tendsto s l atTop) (hN : ∀ᶠ i in l, 0 < N i)
    (γ p C : ℝ) (hp : 0 < p) (hC : 0 < C) :
    ((fun i => C * N i * (s i ^ ((1 + γ) / p) + s i ^ (2 + γ - p))) =o[l]
      fun i => N i * s i) ↔ 1 + γ < p := by
  have hzero : ∀ᶠ i in l, N i * s i = 0 →
      C * N i * (s i ^ ((1 + γ) / p) + s i ^ (2 + γ - p)) = 0 := by
    filter_upwards [hs.eventually (eventually_gt_atTop (0 : ℝ)), hN] with i hi hiN
    exact fun h => False.elim ((mul_pos hiN hi).ne' h)
  exact (Asymptotics.isLittleO_iff_tendsto' hzero).trans
    (excess_bound_ratio_tendsto_zero_iff l s N hs hN γ p C hp hC)

end LPPDifferentiability
