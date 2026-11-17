/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Tactic.Linarith

/-!
# Strict affine support gaps from a square-root boundary expansion

A positive square-root term dominates every linear correction near zero.
Consequently every affine upper bound has intercept strictly above the
constant term of the expansion.
-/

public section

open Set Filter Asymptotics
open scoped Topology NNReal

namespace ProbabilityBasics

/-- A positive square-root boundary expansion forces every affine upper bound
at zero to have a strictly larger intercept. This generic comparison is the
strict-gap step for Martin's boundary expansion and the endpoint interiority
in GRS1510.00860v2, equations (2.6)-(2.8). -/
theorem lt_affine_intercept_of_sqrt_asymptotic
    (f : ℝ≥0 → ℝ) (m sigma p q : ℝ) (hsigma : 0 < sigma)
    (hasym : (fun a : ℝ≥0 => f a - (m + 2 * sigma * Real.sqrt (a : ℝ)))
      =o[𝓝[>] (0 : ℝ≥0)] (fun a : ℝ≥0 => Real.sqrt (a : ℝ)))
    (hupper : ∀ a : ℝ≥0, f a ≤ p + q * (a : ℝ)) : m < p := by
  by_contra hnot
  have hpm : p ≤ m := le_of_not_gt hnot
  -- The right filter contains positive points arbitrarily close to zero.
  have : NeBot (𝓝[>] (0 : ℝ≥0)) :=
    nhdsGT_neBot_of_exists_gt ⟨1, zero_lt_one⟩
  -- The little-o remainder loses at most one sigma times sqrt(a).
  have herror : ∀ᶠ a : ℝ≥0 in 𝓝[>] (0 : ℝ≥0),
      |f a - (m + 2 * sigma * Real.sqrt (a : ℝ))| ≤
        sigma * Real.sqrt (a : ℝ) := by
    filter_upwards [hasym.bound hsigma] with a ha
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using ha
  have hcontinuous : Continuous (fun a : ℝ≥0 => q * Real.sqrt (a : ℝ)) :=
    continuous_const.mul (Real.continuous_sqrt.comp NNReal.continuous_coe)
  have hlimit : Tendsto (fun a : ℝ≥0 => q * Real.sqrt (a : ℝ))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 (0 : ℝ)) := by
    simpa only [NNReal.coe_zero, Real.sqrt_zero, mul_zero] using
      (hcontinuous.tendsto 0).mono_left nhdsWithin_le_nhds
  have hsmall : ∀ᶠ a : ℝ≥0 in 𝓝[>] (0 : ℝ≥0),
      q * Real.sqrt (a : ℝ) < sigma := hlimit.eventually (Iio_mem_nhds hsigma)
  have hevent : ∀ᶠ a : ℝ≥0 in 𝓝[>] (0 : ℝ≥0),
      |f a - (m + 2 * sigma * Real.sqrt (a : ℝ))| ≤ sigma * Real.sqrt (a : ℝ) ∧
        q * Real.sqrt (a : ℝ) < sigma ∧ 0 < a :=
    herror.and (hsmall.and self_mem_nhdsWithin)
  obtain ⟨a, haerror, hasmall, hapos⟩ := hevent.exists
  have hsqrtpos : 0 < Real.sqrt (a : ℝ) := Real.sqrt_pos.mpr (NNReal.coe_pos.mpr hapos)
  have hremainder : -(sigma * Real.sqrt (a : ℝ)) ≤
      f a - (m + 2 * sigma * Real.sqrt (a : ℝ)) := (abs_le.mp haerror).1
  have hlower : m + sigma * Real.sqrt (a : ℝ) ≤ f a := by
    linarith only [hremainder]
  have hlinear : f a ≤ m + q * (a : ℝ) := by
    linarith only [hupper a, hpm]
  have hcompare : sigma * Real.sqrt (a : ℝ) ≤ q * (a : ℝ) := by
    linarith only [hlower, hlinear]
  -- Rewrite the linear term using sqrt(a)^2=a and cancel its positive factor.
  have hproduct : sigma * Real.sqrt (a : ℝ) ≤
      (q * Real.sqrt (a : ℝ)) * Real.sqrt (a : ℝ) := by
    calc
      sigma * Real.sqrt (a : ℝ) ≤ q * (a : ℝ) := hcompare
      _ = (q * Real.sqrt (a : ℝ)) * Real.sqrt (a : ℝ) := by
        rw [mul_assoc, Real.mul_self_sqrt (NNReal.coe_nonneg a)]
  have hsigma_le : sigma ≤ q * Real.sqrt (a : ℝ) :=
    le_of_mul_le_mul_right hproduct hsqrtpos
  exact (not_le_of_gt hasmall) hsigma_le

end ProbabilityBasics
