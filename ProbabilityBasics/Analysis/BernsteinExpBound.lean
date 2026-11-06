/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Scalar exponential bounds for Bernstein's inequality

The exact quadratic remainder has denominator `2 * (1 - x / 3)`.
The first bound includes every negative real input as well as `0 ≤ x < 3`.
-/

public section

namespace LPPDifferentiability

private theorem bernstein_polynomial_nonneg (x : ℝ) :
    0 ≤ 1 + 2 * x / 3 + x ^ 2 / 6 - (1 - x / 3) * Real.exp x := by
  let g : ℝ → ℝ := fun y =>
    1 + 2 * y / 3 + y ^ 2 / 6 - (1 - y / 3) * Real.exp y
  let g' : ℝ → ℝ := fun y => (2 + y - (2 - y) * Real.exp y) / 3
  have hg (y : ℝ) : HasDerivAt g (g' y) y := by
    dsimp [g, g']
    convert (((hasDerivAt_const y 1).add
      (((hasDerivAt_id y).const_mul 2).div_const 3)).add
      (((hasDerivAt_id y).pow 2).div_const 6)).sub
      (((hasDerivAt_const y 1).sub ((hasDerivAt_id y).div_const 3)).mul
        (Real.hasDerivAt_exp y)) using 1
    · funext z
      dsimp
    · dsimp
      ring
  have hg' (y : ℝ) :
      HasDerivAt g' ((1 - (1 - y) * Real.exp y) / 3) y := by
    dsimp [g']
    convert (((hasDerivAt_const y 2).add (hasDerivAt_id y)).sub
      (((hasDerivAt_const y 2).sub (hasDerivAt_id y)).mul
        (Real.hasDerivAt_exp y))).div_const 3 using 1
    · funext z
      dsimp
    · dsimp
      ring
  have hsecond (y : ℝ) : 0 ≤ (1 - (1 - y) * Real.exp y) / 3 := by
    have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-y))
      (Real.exp_nonneg y)
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
    linarith only [h]
  have hconv : ConvexOn ℝ Set.univ g :=
    convexOn_of_hasDerivWithinAt2_nonneg convex_univ
      (fun y _ => (hg y).continuousAt.continuousWithinAt)
      (fun y _ => (hg y).hasDerivWithinAt)
      (fun y _ => (hg' y).hasDerivWithinAt)
      (fun y _ => hsecond y)
  have hg0 : g 0 = 0 := by norm_num [g]
  have hg'0 : HasDerivAt g 0 0 := by
    simpa only [g', Real.exp_zero, sub_zero, mul_one, add_zero, sub_self, zero_div]
      using hg 0
  change 0 ≤ g x
  rcases lt_trichotomy 0 x with hx | hx | hx
  · have hs := hconv.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ x) hx hg'0
    simp only [slope_def_field, hg0, sub_zero] at hs
    simpa only [zero_mul] using (le_div_iff₀ hx).mp hs
  · simpa only [← hx, hg0] using (le_refl (0 : ℝ))
  · have hs := hconv.slope_le_of_hasDerivAt (Set.mem_univ x) (Set.mem_univ 0) hx hg'0
    simp only [slope_def_field, hg0, zero_sub] at hs
    have hn := (div_le_iff₀ (neg_pos.mpr hx)).mp hs
    linarith only [hn]

/-- The exact Bernstein exponential majorant, including all negative inputs. -/
theorem exp_le_one_add_add_sq_div (x : ℝ) (hx : x < 3) :
    Real.exp x ≤ 1 + x + x ^ 2 / (2 * (1 - x / 3)) := by
  have hd : 0 < 1 - x / 3 := by linarith only [hx]
  have hpoly := bernstein_polynomial_nonneg x
  have heq : 1 + x + x ^ 2 / (2 * (1 - x / 3)) =
      (1 + 2 * x / 3 + x ^ 2 / 6) / (1 - x / 3) := by
    field_simp [show 3 - x ≠ 0 by linarith only [hx]]
    ring
  rw [heq]
  apply (le_div_iff₀ hd).2
  linarith only [hpoly]

/-- A uniform denominator valid whenever the input is at most `c < 3`. -/
theorem exp_le_one_add_add_sq_div_of_le (x c : ℝ) (_hc₀ : 0 ≤ c)
    (hc : c < 3) (hxc : x ≤ c) :
    Real.exp x ≤ 1 + x + x ^ 2 / (2 * (1 - c / 3)) := by
  have hx : x < 3 := hxc.trans_lt hc
  have hd : 0 < 2 * (1 - c / 3) := by linarith only [hc]
  have hden : 2 * (1 - c / 3) ≤ 2 * (1 - x / 3) := by
    linarith only [hxc]
  exact (exp_le_one_add_add_sq_div x hx).trans
    (add_le_add (le_refl (1 + x)) (div_le_div_of_nonneg_left (sq_nonneg x) hd hden))

/-- The uniform scalar bound for a nonnegative exponential parameter and `|z| ≤ b`. -/
theorem exp_mul_le_one_add_add_sq_div (b lam z : ℝ) (hb : 0 < b)
    (hlam : 0 ≤ lam) (hsmall : lam * b < 3) (hz : |z| ≤ b) :
    Real.exp (lam * z) ≤ 1 + lam * z +
      lam ^ 2 * z ^ 2 / (2 * (1 - lam * b / 3)) := by
  have hc : 0 ≤ lam * b := mul_nonneg hlam hb.le
  have hzc : lam * z ≤ lam * b :=
    mul_le_mul_of_nonneg_left ((le_abs_self z).trans hz) hlam
  have h := exp_le_one_add_add_sq_div_of_le (lam * z) (lam * b) hc hsmall hzc
  simpa only [mul_pow] using h

end LPPDifferentiability
