/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! # A rational cone estimate

These conditional algebraic lemmas support the interior-continuity step used
with Martin's Proposition 2.1. They neither define a shape nor construct an
extension from rational to real directions.
-/

public section

namespace LPPDifferentiability

/-- A nonnegative superadditive function on the rational quadrant is monotone. -/
theorem nnrat_pair_monotone_of_nonneg_superadditive
    (H : (ℚ≥0 × ℚ≥0) → ℝ)
    (hnonneg : ∀ z, 0 ≤ H z)
    (hadd : ∀ u v, H u + H v ≤ H (u + v)) : Monotone H := by
  intro x y hxy
  have hsum : x + (y - x) = y := by
    exact Prod.ext (add_tsub_cancel_of_le hxy.1) (add_tsub_cancel_of_le hxy.2)
  have h := hadd x (y - x)
  rw [hsum] at h
  exact le_trans (le_add_of_nonneg_right (hnonneg (y - x))) h

private theorem nnrat_cast_tsub_of_le (p q : ℚ≥0) (h : q ≤ p) :
    ((p - q : ℚ≥0) : ℝ) = (p : ℝ) - (q : ℝ) := by
  have heq := congrArg (fun t : ℚ≥0 => (t : ℝ)) (add_tsub_cancel_of_le h)
  rw [NNRat.cast_add] at heq
  linarith only [heq]

private theorem nnrat_cast_max_tsub (p q : ℚ≥0) :
    ((max (p - q) (q - p) : ℚ≥0) : ℝ) = |(p : ℝ) - (q : ℝ)| := by
  by_cases h : p ≤ q
  · rw [tsub_eq_zero_of_le h, max_eq_right (zero_le), nnrat_cast_tsub_of_le q p h,
      abs_of_nonpos (sub_nonpos.mpr (NNRat.cast_le.mpr h))]
    ring
  · have hqp : q ≤ p := le_of_not_ge h
    rw [tsub_eq_zero_of_le hqp, max_eq_left (zero_le), nnrat_cast_tsub_of_le p q hqp,
      abs_of_nonneg (sub_nonneg.mpr (NNRat.cast_le.mpr hqp))]

/-- Quantitative continuity on a rational box bounded away from the axes.
All coordinate and scalar casts in the estimate are casts to the real numbers.
No strict positivity of the upper-bound constant is required. -/
theorem nnrat_pair_abs_sub_le_of_monotone_homogeneous
    (H : (ℚ≥0 × ℚ≥0) → ℝ) (hmono : Monotone H)
    (hhom : ∀ (c : ℚ≥0) (z : ℚ≥0 × ℚ≥0), H (c • z) = (c : ℝ) * H z)
    (C : ℝ) (hC : 0 ≤ C)
    (hupper : ∀ z : ℚ≥0 × ℚ≥0, H z ≤ C * ((z.1 : ℝ) + (z.2 : ℝ)))
    (a b : ℚ≥0) (ha : 0 < a)
    (x y : ℚ≥0 × ℚ≥0)
    (hax : a ≤ x.1 ∧ a ≤ x.2) (hxb : x.1 ≤ b ∧ x.2 ≤ b)
    (hay : a ≤ y.1 ∧ a ≤ y.2) (hyb : y.1 ≤ b ∧ y.2 ≤ b) :
    |H x - H y| ≤ (2 * (b : ℝ) * C / (a : ℝ)) *
      max (|(x.1 : ℝ) - (y.1 : ℝ)|) (|(x.2 : ℝ) - (y.2 : ℝ)|) := by
  let δ : ℚ≥0 := max (max (x.1 - y.1) (y.1 - x.1))
    (max (x.2 - y.2) (y.2 - x.2))
  have hδ : (δ : ℝ) =
      max (|(x.1 : ℝ) - (y.1 : ℝ)|) (|(x.2 : ℝ) - (y.2 : ℝ)|) := by
    dsimp [δ]
    rw [NNRat.cast_max, nnrat_cast_max_tsub, nnrat_cast_max_tsub]
  have haR : 0 < (a : ℝ) := NNRat.cast_pos.mpr ha
  have hδR : 0 ≤ (δ : ℝ) := NNRat.cast_nonneg δ
  have hratio : 0 ≤ (δ : ℝ) / (a : ℝ) := div_nonneg hδR haR.le
  have hcoord (u v : ℚ≥0) (hau : a ≤ u) (hvu : v - u ≤ δ) :
      v ≤ (1 + δ / a) * u := by
    have hv : v ≤ δ + u := tsub_le_iff_right.mp hvu
    have hscale : δ ≤ δ / a * u := by
      calc
        δ = δ / a * a := (div_mul_cancel₀ δ (ne_of_gt ha)).symm
        _ ≤ δ / a * u := mul_le_mul_of_nonneg_left hau (zero_le)
    calc
      v ≤ δ + u := hv
      _ ≤ δ / a * u + u := by simpa only [add_comm] using add_le_add_right hscale u
      _ = (1 + δ / a) * u := by ring
  have hyx : y ≤ (1 + δ / a) • x := by
    constructor
    · exact hcoord x.1 y.1 hax.1
        (le_trans (le_max_right _ _) (le_max_left _ _))
    · exact hcoord x.2 y.2 hax.2
        (le_trans (le_max_right _ _) (le_max_right _ _))
  have hxy : x ≤ (1 + δ / a) • y := by
    constructor
    · exact hcoord y.1 x.1 hay.1
        (le_trans (le_max_left _ _) (le_max_left _ _))
    · exact hcoord y.2 x.2 hay.2
        (le_trans (le_max_left _ _) (le_max_right _ _))
  have honeway (u v : ℚ≥0 × ℚ≥0) (hub : u.1 ≤ b ∧ u.2 ≤ b)
      (hvu : v ≤ (1 + δ / a) • u) :
      H v - H u ≤ (2 * (b : ℝ) * C / (a : ℝ)) * (δ : ℝ) := by
    have hm := hmono hvu
    rw [hhom, NNRat.cast_add, NNRat.cast_one, NNRat.cast_div] at hm
    have hu : H u ≤ 2 * (b : ℝ) * C := by
      calc
        H u ≤ C * ((u.1 : ℝ) + (u.2 : ℝ)) := hupper u
        _ ≤ C * ((b : ℝ) + (b : ℝ)) := mul_le_mul_of_nonneg_left
          (add_le_add (NNRat.cast_le.mpr hub.1) (NNRat.cast_le.mpr hub.2)) hC
        _ = 2 * (b : ℝ) * C := by ring
    have hmul := mul_le_mul_of_nonneg_left hu hratio
    calc
      H v - H u ≤ ((δ : ℝ) / (a : ℝ)) * H u := by linarith only [hm]
      _ ≤ ((δ : ℝ) / (a : ℝ)) * (2 * (b : ℝ) * C) := hmul
      _ = (2 * (b : ℝ) * C / (a : ℝ)) * (δ : ℝ) := by ring
  rw [← hδ, abs_sub_le_iff]
  exact ⟨honeway y x hyb hxy, honeway x y hxb hyx⟩

end LPPDifferentiability
