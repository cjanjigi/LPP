/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Peierls contour series

The scalar series in the final counting step of the Peierls argument is
summable and has sum less than one for a suitable cutoff depending on `k`.
-/

public section

namespace LPPDifferentiability

private theorem nat_add_six_sq_le_four_pow (n : ℕ) :
    (n + 6) ^ 2 ≤ 4 ^ (n + 4) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hstep : (n + 7) ^ 2 ≤ 4 * (n + 6) ^ 2 := by
      nlinarith [Nat.zero_le n]
    calc
      (Nat.succ n + 6) ^ 2 = (n + 7) ^ 2 := by
        simp [Nat.succ_eq_add_one, Nat.add_assoc]
      _ ≤ 4 * (n + 6) ^ 2 := hstep
      _ ≤ 4 * 4 ^ (n + 4) := Nat.mul_le_mul_left 4 ih
      _ = 4 ^ (n + 4 + 1) := by rw [pow_succ]; ring
      _ = 4 ^ (Nat.succ n + 4) := by
        congr 1

private theorem peierls_polynomial_bound (n : ℕ) :
    ((n + 6 : ℕ) : ℝ) ^ 2 ≤ (4 : ℝ) ^ (n + 4) := by
  exact_mod_cast nat_add_six_sq_le_four_pow n

/-- For every natural number `k`, the shifted contour series is summable
and has sum less than one for some cutoff in `(0, 1)`. -/
theorem exists_peierls_contour_series_bound (k : ℕ) :
    ∃ ζ : ℝ, 0 < ζ ∧ ζ < 1 ∧
      Summable (fun n : ℕ =>
        ((n + 6 : ℕ) : ℝ) ^ 2 * 4 *
          (3 * ζ ^ (1 / (8 * (((2 * k + 1) ^ 2 : ℕ) : ℝ))) : ℝ) ^ (n + 3) *
            ζ ^ (1 / (8 * (((2 * k + 1) ^ 2 : ℕ) : ℝ)))) ∧
      (∑' n : ℕ,
        ((n + 6 : ℕ) : ℝ) ^ 2 * 4 *
          (3 * ζ ^ (1 / (8 * (((2 * k + 1) ^ 2 : ℕ) : ℝ))) : ℝ) ^ (n + 3) *
            ζ ^ (1 / (8 * (((2 * k + 1) ^ 2 : ℕ) : ℝ)))) < 1 := by
  let C : ℕ := 8 * (2 * k + 1) ^ 2
  let ρ : ℝ := 1 / 48
  let ζ : ℝ := ρ ^ C
  have hCpos : 0 < C := by
    dsimp [C]
    positivity
  have hCne : C ≠ 0 := Nat.ne_of_gt hCpos
  have hCcast : (C : ℝ) = 8 * (((2 * k + 1) ^ 2 : ℕ) : ℝ) := by
    dsimp [C]
    push_cast
    ring
  have hζpos : 0 < ζ := by
    dsimp [ζ, ρ]
    positivity
  have hζlt : ζ < 1 := by
    dsimp [ζ, ρ]
    exact pow_lt_one₀ (by norm_num) (by norm_num) hCne
  have hexponent :
      (1 : ℝ) / (8 * (((2 * k + 1) ^ 2 : ℕ) : ℝ)) = (C : ℝ)⁻¹ := by
    rw [hCcast]
    simp only [one_div]
  have hroot : ζ ^ (1 / (8 * (((2 * k + 1) ^ 2 : ℕ) : ℝ))) = ρ := by
    change ((1 / 48 : ℝ) ^ C) ^
      (1 / (8 * (((2 * k + 1) ^ 2 : ℕ) : ℝ))) = 1 / 48
    rw [hexponent]
    exact Real.pow_rpow_inv_natCast (by norm_num) hCne
  let seriesTerm : ℕ → ℝ := fun n =>
    ((n + 6 : ℕ) : ℝ) ^ 2 * 4 *
      (3 * ζ ^ (1 / (8 * (((2 * k + 1) ^ 2 : ℕ) : ℝ))) : ℝ) ^ (n + 3) *
        ζ ^ (1 / (8 * (((2 * k + 1) ^ 2 : ℕ) : ℝ)))
  let geometricTerm : ℕ → ℝ := fun n => (1 / 192 : ℝ) * (1 / 4 : ℝ) ^ n
  have geometricHasSum : HasSum (fun n : ℕ => (1 / 4 : ℝ) ^ n)
      (1 - (1 / 4 : ℝ))⁻¹ :=
    hasSum_geometric_of_lt_one (by norm_num) (by norm_num)
  have geometricScaledHasSum :
      HasSum geometricTerm ((1 / 192 : ℝ) * (1 - (1 / 4 : ℝ))⁻¹) := by
    simpa only [geometricTerm] using geometricHasSum.mul_left (1 / 192 : ℝ)
  have geometricSummable : Summable geometricTerm := geometricScaledHasSum.summable
  have geometricTsum : (∑' n : ℕ, geometricTerm n) = 1 / 144 := by
    calc
      _ = (1 / 192 : ℝ) * (1 - (1 / 4 : ℝ))⁻¹ := geometricScaledHasSum.tsum_eq
      _ = 1 / 144 := by norm_num
  have sourceNonneg : ∀ n : ℕ, 0 ≤ seriesTerm n := by
    intro n
    dsimp [seriesTerm]
    positivity
  have sourceLeGeometric : ∀ n : ℕ, seriesTerm n ≤ geometricTerm n := by
    intro n
    dsimp [seriesTerm, geometricTerm]
    rw [hroot, show (3 : ℝ) * (1 / 48 : ℝ) = (1 / 16 : ℝ) by norm_num]
    calc
      _ = ((n + 6 : ℕ) : ℝ) ^ 2 *
          (4 * (1 / 16 : ℝ) ^ (n + 3) * (1 / 48 : ℝ)) := by ring
      _ ≤ (4 : ℝ) ^ (n + 4) *
          (4 * (1 / 16 : ℝ) ^ (n + 3) * (1 / 48 : ℝ)) :=
        mul_le_mul_of_nonneg_right (peierls_polynomial_bound n) (by positivity)
      _ = (4 : ℝ) ^ (n + 4) * 4 * (1 / 16 : ℝ) ^ (n + 3) * (1 / 48 : ℝ) := by ring
      _ = (1 / 192 : ℝ) * (1 / 4 : ℝ) ^ n := by
        rw [pow_add, pow_add]
        calc
          _ = ((4 : ℝ) ^ n * (1 / 16 : ℝ) ^ n) *
              ((4 : ℝ) ^ 4 * 4 * (1 / 16 : ℝ) ^ 3 * (1 / 48 : ℝ)) := by ring
          _ = (4 * (1 / 16 : ℝ)) ^ n *
              ((4 : ℝ) ^ 4 * 4 * (1 / 16 : ℝ) ^ 3 * (1 / 48 : ℝ)) := by
            rw [← mul_pow]
          _ = (1 / 192 : ℝ) * (1 / 4 : ℝ) ^ n := by
            norm_num
            ring
  have seriesSummable : Summable seriesTerm :=
    Summable.of_nonneg_of_le sourceNonneg sourceLeGeometric geometricSummable
  have seriesTsumLt : (∑' n : ℕ, seriesTerm n) < 1 := by
    calc
      _ ≤ ∑' n : ℕ, geometricTerm n :=
        seriesSummable.tsum_le_tsum sourceLeGeometric geometricSummable
      _ = 1 / 144 := geometricTsum
      _ < 1 := by norm_num
  refine ⟨ζ, hζpos, hζlt, ?_⟩
  exact ⟨seriesSummable, seriesTsumLt⟩

end LPPDifferentiability

end
