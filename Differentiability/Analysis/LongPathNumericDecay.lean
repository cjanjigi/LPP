/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Long-path scalar decay

The scalar estimate used after the itinerary and allocation counts in the
source proof of the long-path proposition.
-/

public section

namespace LPPDifferentiability

private theorem long_path_root_power_identity (x : ℝ) (hx : 0 ≤ x) :
    (x ^ (1 / 32 : ℝ)) ^ (32 : ℕ) = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

private theorem long_path_fractional_power_nat (x : ℝ) (hx : 0 ≤ x) (N : ℕ) :
    (x ^ (1 / 32 : ℝ)) ^ N = x ^ ((N : ℝ) / 32) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1
  ring

/-- The exact scalar estimate following the source's itinerary and allocation
counts. Positivity and the displayed numerical condition alone force `2*q0`
into `(0, 1)`, so the estimate also covers `N = 0` without another premise.
-/
theorem long_path_numeric_decay (q0 : ℝ) (hq0 : 0 < q0)
    (hsmall : 60 * (2 * q0) ^ (1 / 32 : ℝ) ≤ 1 / 2) (N : ℕ) :
    (15 ^ N * 4 ^ N * (2 * q0) ^ ((N / 32 : ℕ) : ℝ) ≤
      (2 * q0) ^ (-1 : ℝ) * (60 * (2 * q0) ^ (1 / 32 : ℝ)) ^ N) ∧
    ((2 * q0) ^ (-1 : ℝ) * (60 * (2 * q0) ^ (1 / 32 : ℝ)) ^ N ≤
      (2 * q0) ^ (-1 : ℝ) * (1 / 2 : ℝ) ^ N) := by
  let x : ℝ := 2 * q0
  have hx : 0 < x := by
    dsimp [x]
    positivity
  have hsmall' : 60 * x ^ (1 / 32 : ℝ) ≤ 1 / 2 := by
    simpa [x] using hsmall
  have hxroot : 0 < x ^ (1 / 32 : ℝ) := Real.rpow_pos_of_pos hx _
  have hxroot_le : x ^ (1 / 32 : ℝ) ≤ 1 / 120 := by
    nlinarith [hsmall']
  have hxroot_power := long_path_root_power_identity x hx.le
  have hx_lt_one : x < 1 := by
    calc
      x = (x ^ (1 / 32 : ℝ)) ^ (32 : ℕ) := hxroot_power.symm
      _ ≤ (1 / 120 : ℝ) ^ (32 : ℕ) :=
        pow_le_pow_left₀ hxroot.le hxroot_le _
      _ < 1 := by norm_num
  have hfloor : ((N / 32 : ℕ) : ℝ) ≥ (N : ℝ) / 32 - 1 := by
    have hdivmod : ((N % 32 : ℕ) : ℝ) + 32 * ((N / 32 : ℕ) : ℝ) = (N : ℝ) := by
      exact_mod_cast Nat.mod_add_div N 32
    have hmod : ((N % 32 : ℕ) : ℝ) < 32 := by
      exact_mod_cast Nat.mod_lt N (by norm_num)
    nlinarith
  have hfloor_power :
      x ^ ((N / 32 : ℕ) : ℝ) ≤ x ^ ((N : ℝ) / 32 - 1) :=
    Real.rpow_le_rpow_of_exponent_ge hx hx_lt_one.le hfloor
  have hroot_power_nat :
      (x ^ (1 / 32 : ℝ)) ^ N = x ^ ((N : ℝ) / 32) :=
    long_path_fractional_power_nat x hx.le N
  constructor
  · calc
      15 ^ N * 4 ^ N * x ^ ((N / 32 : ℕ) : ℝ) =
          (60 : ℝ) ^ N * x ^ ((N / 32 : ℕ) : ℝ) := by
            rw [← mul_pow]
            norm_num
      _ ≤ (60 : ℝ) ^ N * x ^ ((N : ℝ) / 32 - 1) :=
        mul_le_mul_of_nonneg_left hfloor_power (by positivity)
      _ = x ^ (-1 : ℝ) * (60 * x ^ (1 / 32 : ℝ)) ^ N := by
        rw [mul_pow, hroot_power_nat, Real.rpow_neg_one, Real.rpow_sub_one hx.ne']
        ring
  · have hpow : (60 * x ^ (1 / 32 : ℝ)) ^ N ≤ (1 / 2 : ℝ) ^ N :=
      pow_le_pow_left₀ (by positivity) hsmall' N
    exact mul_le_mul_of_nonneg_left hpow (by positivity)

end LPPDifferentiability
