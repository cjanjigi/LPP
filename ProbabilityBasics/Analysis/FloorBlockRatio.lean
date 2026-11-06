/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Limits for natural block quotients

For a fixed positive block length, the number of sites in the complete blocks
of an interval is asymptotic to the interval length. These limits support
finite block comparisons and their expectation normalizations.
-/

public section

open Filter
open scoped Topology

namespace LPPDifferentiability

/-- The length covered by the complete blocks of size `k`, divided by `n`,
tends to one. The value of the sequence at `n = 0` does not affect this limit. -/
theorem tendsto_nat_div_mul_div {k : ℕ} (hk : 0 < k) :
    Tendsto (fun n : ℕ => (((n / k) * k : ℕ) : ℝ) / (n : ℝ))
      atTop (𝓝 1) := by
  have hrem : Tendsto (fun n : ℕ => ((n % k : ℕ) : ℝ) / (n : ℝ))
      atTop (𝓝 0) := tendsto_mod_div_atTop_nhds_zero_nat hk
  have hratio : Tendsto
      (fun n : ℕ => 1 - ((n % k : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 1) :=
    by simpa only [sub_zero] using tendsto_const_nhds.sub hrem
  apply hratio.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hdivmod : (n / k) * k + n % k = n := by
    rw [Nat.mul_comm (n / k) k]
    exact Nat.div_add_mod n k
  have hdecomp : (((n / k) * k + n % k : ℕ) : ℝ) = (n : ℝ) := by
    exact congrArg (fun m : ℕ => (m : ℝ)) hdivmod
  have hblock : (((n / k) * k : ℕ) : ℝ) =
      (n : ℝ) - ((n % k : ℕ) : ℝ) := by
    rw [eq_sub_iff_add_eq]
    simpa only [Nat.cast_add, Nat.cast_mul] using hdecomp
  symm
  calc
    (((n / k) * k : ℕ) : ℝ) / (n : ℝ) =
        ((n : ℝ) - ((n % k : ℕ) : ℝ)) / (n : ℝ) := by rw [hblock]
    _ = (n : ℝ) / (n : ℝ) - ((n % k : ℕ) : ℝ) / (n : ℝ) := by rw [sub_div]
    _ = 1 - ((n % k : ℕ) : ℝ) / (n : ℝ) := by rw [div_self hn0]

/-- A convergent real sequence remains convergent after the natural quotient
`n / k` is substituted, and multiplication by the complete-block ratio
preserves its limit. No sign condition is needed on the sequence or its limit. -/
theorem tendsto_nat_div_block_ratio_mul_comp
    {b : ℕ → ℝ} {a : ℝ} {k : ℕ} (hk : 0 < k)
    (hb : Tendsto b atTop (𝓝 a)) :
    Tendsto (fun n : ℕ =>
      ((((n / k) * k : ℕ) : ℝ) / (n : ℝ)) * b (n / k)) atTop (𝓝 a) := by
  have hquot : Tendsto (fun n : ℕ => n / k) atTop atTop :=
    Nat.tendsto_div_const_atTop (Nat.ne_of_gt hk)
  simpa only [Function.comp_apply, one_mul] using
    (tendsto_nat_div_mul_div hk).mul (hb.comp hquot)

end LPPDifferentiability
