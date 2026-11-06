/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Scalar constants for the concentration estimate (Martin (2004), Lemma 3.1)

This module proves only the numerical weakening and its positive-parameter
normalization. It does not assert a probability or passage-maximal estimate.
-/

public section

namespace LPPDifferentiability

/-- The two-sided Hoeffding tail is numerically bounded by the exponential
form used in the centered passage estimate (Martin (2004), Lemma 3.1). -/
theorem two_mul_exp_neg_div_eight_le_exp_sixty_four_sub_div_sixty_four
    (v : ℝ) (hv : 0 ≤ v) :
    2 * Real.exp (-v / 8) ≤ Real.exp (64 - v / 64) := by
  have harg : -v / 8 ≤ -v / 64 := by
    linarith
  have hexp : Real.exp (-v / 8) ≤ Real.exp (-v / 64) :=
    Real.exp_le_exp.mpr harg
  have htwo : (2 : ℝ) ≤ Real.exp 64 := by
    linarith [Real.add_one_le_exp (64 : ℝ)]
  calc
    2 * Real.exp (-v / 8) ≤ 2 * Real.exp (-v / 64) :=
      mul_le_mul_of_nonneg_left hexp (by linarith)
    _ ≤ Real.exp 64 * Real.exp (-v / 64) :=
      mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
    _ = Real.exp (64 - v / 64) := by
      rw [sub_eq_add_neg, neg_div, ← Real.exp_add]

/-- Substitute `u^2 / (n * L^2)` into the scalar estimate when the natural
length and real bound are positive. The threshold `u` is unrestricted. -/
theorem two_mul_exp_neg_u_sq_div_eight_n_l_sq_le_exp_sixty_four_sub_u_sq_div_sixty_four_n_l_sq
    (n : ℕ) (hn : 0 < n) (L : ℝ) (hL : 0 < L) (u : ℝ) :
    2 * Real.exp (-u ^ 2 / (8 * (n : ℝ) * L ^ 2)) ≤
      Real.exp (64 - u ^ 2 / (64 * (n : ℝ) * L ^ 2)) := by
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hden : (0 : ℝ) < (n : ℝ) * L ^ 2 := mul_pos hnR (sq_pos_of_pos hL)
  have hden_ne : (n : ℝ) * L ^ 2 ≠ 0 := ne_of_gt hden
  have hv : 0 ≤ u ^ 2 / ((n : ℝ) * L ^ 2) :=
    div_nonneg (sq_nonneg u) hden.le
  have h := two_mul_exp_neg_div_eight_le_exp_sixty_four_sub_div_sixty_four
    (u ^ 2 / ((n : ℝ) * L ^ 2)) hv
  have hleft :
      -(u ^ 2 / ((n : ℝ) * L ^ 2)) / 8 =
        -u ^ 2 / (8 * (n : ℝ) * L ^ 2) := by
    field_simp [hden_ne]
  have hright :
      64 - (u ^ 2 / ((n : ℝ) * L ^ 2)) / 64 =
        64 - u ^ 2 / (64 * (n : ℝ) * L ^ 2) := by
    field_simp [hden_ne]
  simpa only [hleft, hright] using h

end LPPDifferentiability
