/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Analysis.RationalRateExistence
public import ProbabilityBasics.Analysis.RationalConeLipschitz
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Signed mean correction on rational boxes

These conditional algebraic lemmas apply a signed linear correction to a
rationally homogeneous superadditive rate. They neither define a rate nor
construct a shape or a real extension.
-/

public section

open scoped NNRat

namespace LPPDifferentiability

/-- Signed linear bounds force the correction by the lower mean to satisfy
the rational cone estimate, and adding the mean back gives the signed local
Lipschitz bound on any rational box away from the axes. -/
theorem nnrat_rate_signed_mean_local_lipschitz
    (F : (ℚ≥0 × ℚ≥0) → ℝ)
    (hhom : ∀ (c : ℚ≥0) (q : ℚ≥0 × ℚ≥0),
      F (c • q) = (c : ℝ) * F q)
    (hadd : ∀ q r : ℚ≥0 × ℚ≥0, F q + F r ≤ F (q + r))
    (m M : ℝ)
    (hlo : ∀ q : ℚ≥0 × ℚ≥0,
      m * ((q.1 : ℝ) + (q.2 : ℝ)) ≤ F q)
    (hup : ∀ q : ℚ≥0 × ℚ≥0,
      F q ≤ M * ((q.1 : ℝ) + (q.2 : ℝ)))
    (a b : ℚ≥0) (ha : 0 < a)
    (x y : ℚ≥0 × ℚ≥0)
    (hax : a ≤ x.1 ∧ a ≤ x.2) (hxb : x.1 ≤ b ∧ x.2 ≤ b)
    (hay : a ≤ y.1 ∧ a ≤ y.2) (hyb : y.1 ≤ b ∧ y.2 ≤ b) :
    |F x - F y| ≤
      (2 * (b : ℝ) * (M - m) / (a : ℝ) + 2 * |m|) *
        max (|(x.1 : ℝ) - (y.1 : ℝ)|) (|(x.2 : ℝ) - (y.2 : ℝ)|) := by
  let length : (ℚ≥0 × ℚ≥0) → ℝ := fun q => (q.1 : ℝ) + (q.2 : ℝ)
  let H : (ℚ≥0 × ℚ≥0) → ℝ := fun q => F q - m * length q
  have hlength_add (q r : ℚ≥0 × ℚ≥0) : length (q + r) = length q + length r := by
    dsimp [length]
    simp only [NNRat.cast_add]
    ring
  have hmM : m ≤ M := by
    have hlo₁ := hlo (1, 0)
    have hup₁ := hup (1, 0)
    have hmF : m ≤ F (1, 0) := by simpa [length] using hlo₁
    have hFM : F (1, 0) ≤ M := by simpa [length] using hup₁
    exact le_trans hmF hFM
  let C : ℝ := M - m
  have hC : 0 ≤ C := by
    dsimp [C]
    exact sub_nonneg.mpr hmM
  have hHnonneg : ∀ q : ℚ≥0 × ℚ≥0, 0 ≤ H q := by
    intro q
    change 0 ≤ F q - m * length q
    exact sub_nonneg.mpr (hlo q)
  have hHupper : ∀ q : ℚ≥0 × ℚ≥0, H q ≤ C * length q := by
    intro q
    change F q - m * length q ≤ (M - m) * length q
    calc
      F q - m * length q ≤ M * length q - m * length q :=
        sub_le_sub_right (hup q) (m * length q)
      _ = (M - m) * length q := by ring
  have hHhom : ∀ (c : ℚ≥0) (q : ℚ≥0 × ℚ≥0),
      H (c • q) = (c : ℝ) * H q := by
    intro c q
    change F (c • q) - m * length (c • q) =
      (c : ℝ) * (F q - m * length q)
    rw [hhom c q]
    dsimp [length]
    simp only [NNRat.cast_mul]
    ring
  have hHadd : ∀ q r : ℚ≥0 × ℚ≥0, H q + H r ≤ H (q + r) := by
    intro q r
    change (F q - m * length q) + (F r - m * length r) ≤
      F (q + r) - m * length (q + r)
    rw [hlength_add q r]
    linarith [hadd q r]
  have hHmono : Monotone H :=
    nnrat_pair_monotone_of_nonneg_superadditive H hHnonneg hHadd
  have hHlip := nnrat_pair_abs_sub_le_of_monotone_homogeneous
    H hHmono hHhom C hC hHupper a b ha x y hax hxb hay hyb
  have hlength_diff :
      |length x - length y| ≤
        2 * max (|(x.1 : ℝ) - (y.1 : ℝ)|)
          (|(x.2 : ℝ) - (y.2 : ℝ)|) := by
    dsimp [length]
    have h₁ : |(x.1 : ℝ) - (y.1 : ℝ)| ≤
        max (|(x.1 : ℝ) - (y.1 : ℝ)|) (|(x.2 : ℝ) - (y.2 : ℝ)|) := le_max_left _ _
    have h₂ : |(x.2 : ℝ) - (y.2 : ℝ)| ≤
        max (|(x.1 : ℝ) - (y.1 : ℝ)|) (|(x.2 : ℝ) - (y.2 : ℝ)|) := le_max_right _ _
    calc
      |((x.1 : ℝ) + x.2) - ((y.1 : ℝ) + y.2)| =
          |((x.1 : ℝ) - (y.1 : ℝ)) + ((x.2 : ℝ) - (y.2 : ℝ))| := by congr 1; ring
      _ ≤ |(x.1 : ℝ) - (y.1 : ℝ)| + |(x.2 : ℝ) - (y.2 : ℝ)| := abs_add_le _ _
      _ ≤ 2 * max (|(x.1 : ℝ) - (y.1 : ℝ)|)
          (|(x.2 : ℝ) - (y.2 : ℝ)|) := by linarith
  have hmean :
      |m * (length x - length y)| ≤
        2 * |m| * max (|(x.1 : ℝ) - (y.1 : ℝ)|)
          (|(x.2 : ℝ) - (y.2 : ℝ)|) := by
    rw [abs_mul]
    calc
      |m| * |length x - length y| ≤
          |m| * (2 * max (|(x.1 : ℝ) - (y.1 : ℝ)|)
            (|(x.2 : ℝ) - (y.2 : ℝ)|)) :=
        mul_le_mul_of_nonneg_left hlength_diff (abs_nonneg m)
      _ = 2 * |m| * max (|(x.1 : ℝ) - (y.1 : ℝ)|)
          (|(x.2 : ℝ) - (y.2 : ℝ)|) := by ring
  have hdecomp :
      F x - F y = (H x - H y) + m * (length x - length y) := by
    dsimp [H]
    ring
  calc
    |F x - F y| = |(H x - H y) + m * (length x - length y)| :=
      congrArg abs hdecomp
    _ ≤ |H x - H y| + |m * (length x - length y)| := abs_add_le _ _
    _ ≤ (2 * (b : ℝ) * C / (a : ℝ)) *
          max (|(x.1 : ℝ) - (y.1 : ℝ)|) (|(x.2 : ℝ) - (y.2 : ℝ)|) +
        2 * |m| * max (|(x.1 : ℝ) - (y.1 : ℝ)|)
          (|(x.2 : ℝ) - (y.2 : ℝ)|) := add_le_add hHlip hmean
    _ = (2 * (b : ℝ) * (M - m) / (a : ℝ) + 2 * |m|) *
          max (|(x.1 : ℝ) - (y.1 : ℝ)|) (|(x.2 : ℝ) - (y.2 : ℝ)|) := by
      dsimp [C]
      ring

end LPPDifferentiability
