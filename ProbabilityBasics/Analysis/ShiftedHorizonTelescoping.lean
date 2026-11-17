/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Finite telescoping across signed levels

These identities sum one-based increments over a finite horizon. They give the
algebraic averaging step in the corrected signed-level form of JR (4.17),
without any probability or integrability assumptions.
-/

public section

namespace ProbabilityBasics

/-- The one-based increments telescope at every signed level. This is the
finite algebra behind the corrected signed-level average in JR (4.17). -/
theorem sum_finite_shifted_increments (f : ℕ → ℝ) (m : ℤ) (t : ℝ) (M : ℕ) :
    (∑ k : Fin M, (if m < (k.val : ℤ) + 1 then
      f (((k.val : ℤ) + 1 - m).toNat) - f (((k.val : ℤ) - m).toNat) - t
    else 0)) =
      f (((M : ℤ) - m).toNat) - f ((-m).toNat) -
        ((((M : ℤ) - max m 0).toNat : ℕ) : ℝ) * t := by
  induction M with
  | zero =>
      -- The empty window has no increments or tilt terms.
      simp only [Finset.univ_eq_empty, Finset.sum_empty, Nat.cast_zero]
      by_cases hm : m ≤ 0
      · have htop : ((0 : ℤ) - m).toNat = (-m).toNat := by
          congr 1
          omega
        have hcount : ((0 : ℤ) - max m 0).toNat = 0 := by
          rw [max_eq_right hm]
          rfl
        rw [htop, hcount]
        ring
      · have hmpos : 0 < m := by omega
        have htop : ((0 : ℤ) - m).toNat = 0 := by omega
        have hbottom : (-m).toNat = 0 := by omega
        have hcount : ((0 : ℤ) - max m 0).toNat = 0 := by
          rw [max_eq_left (le_of_lt hmpos)]
          omega
        rw [htop, hbottom, hcount]
        ring
  | succ M ih =>
      -- Appending the last index leaves one new increment.
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, Nat.cast_succ]
      by_cases hactive : m < (M : ℤ) + 1
      · -- An active last index extends both the horizon and tilt count by one.
        have hmle : m ≤ (M : ℤ) := by omega
        have htop_nonneg : 0 ≤ (M : ℤ) - m := by omega
        have htopInt : ((((M : ℤ) + 1 - m).toNat : ℕ) : ℤ) =
            ((((M : ℤ) - m).toNat + 1 : ℕ) : ℤ) := by
          rw [Int.natCast_add, Int.natCast_one,
            Int.toNat_of_nonneg (by omega : 0 ≤ (M : ℤ) + 1 - m),
            Int.toNat_of_nonneg htop_nonneg]
          omega
        have htop : ((M : ℤ) + 1 - m).toNat = ((M : ℤ) - m).toNat + 1 := by
          exact_mod_cast htopInt
        have hcount : (((M : ℤ) + 1 - max m 0).toNat) =
            (((M : ℤ) - max m 0).toNat) + 1 := by
          by_cases hmnonpos : m ≤ 0
          · have hcountInt :
                ((((M : ℤ) + 1 - max m 0).toNat : ℕ) : ℤ) =
                  ((((M : ℤ) - max m 0).toNat + 1 : ℕ) : ℤ) := by
              rw [max_eq_right hmnonpos, Int.natCast_add, Int.natCast_one,
                Int.toNat_of_nonneg (by omega : 0 ≤ (M : ℤ) + 1 - 0),
                Int.toNat_of_nonneg (by omega : 0 ≤ (M : ℤ) - 0)]
              omega
            exact_mod_cast hcountInt
          · have hmpos : 0 < m := by omega
            have hcountInt :
                ((((M : ℤ) + 1 - max m 0).toNat : ℕ) : ℤ) =
                  ((((M : ℤ) - max m 0).toNat + 1 : ℕ) : ℤ) := by
              rw [max_eq_left (le_of_lt hmpos), Int.natCast_add, Int.natCast_one,
                Int.toNat_of_nonneg (by omega : 0 ≤ (M : ℤ) + 1 - m),
                Int.toNat_of_nonneg htop_nonneg]
              omega
            exact_mod_cast hcountInt
        rw [ih, ite_eq_left hactive, htop, hcount]
        simp only [Nat.cast_add, Nat.cast_one]
        ring
      · -- Beyond the active window all endpoint indices and counts are zero.
        have hmlo : (M : ℤ) + 1 ≤ m := by omega
        have htopPrev : ((M : ℤ) - m).toNat = 0 := by omega
        have htopNow : ((M : ℤ) + 1 - m).toNat = 0 := by omega
        have hbottom : (-m).toNat = 0 := by omega
        have hcountPrev : ((M : ℤ) - max m 0).toNat = 0 := by
          rw [max_eq_left (by omega : 0 ≤ m)]
          omega
        have hcountNow : ((M : ℤ) + 1 - max m 0).toNat = 0 := by
          rw [max_eq_left (by omega : 0 ≤ m)]
          omega
        rw [ih, ite_eq_right hactive, htopPrev, htopNow, hbottom, hcountPrev, hcountNow]
        ring

/-- Averaging the one-based increments gives the corrected finite signed-level
formula of JR (4.17), under its positive-window condition. -/
theorem average_finite_shifted_increments (f : ℕ → ℝ) (m : ℤ) (t : ℝ) (M : ℕ)
    (hwindow : max m 0 < (M : ℤ)) :
    (∑ k : Fin M, (if m < (k.val : ℤ) + 1 then
      f (((k.val : ℤ) + 1 - m).toNat) - f (((k.val : ℤ) - m).toNat) - t
    else 0)) / (M : ℝ) =
      (f (((M : ℤ) - m).toNat) - f ((max (-m) 0).toNat) -
        ((M : ℝ) - (max m 0 : ℝ)) * t) / (M : ℝ) := by
  -- The corrected boundary is fixed at the negative part of the level.
  have hboundary : (-m).toNat = (max (-m) 0).toNat := by
    by_cases hm : m ≤ 0
    · rw [max_eq_left (by omega : 0 ≤ -m)]
    · have hmpos : 0 < m := by omega
      have hnegative : (-m).toNat = 0 := by omega
      rw [max_eq_right (by omega : -m ≤ 0), hnegative]
      rfl
  -- The positive-window assumption converts the natural count to a real count.
  have hcountInt : (((M : ℤ) - max m 0).toNat : ℤ) = (M : ℤ) - max m 0 := by
    rw [Int.toNat_of_nonneg (by omega : 0 ≤ (M : ℤ) - max m 0)]
  have hcountReal : ((((M : ℤ) - max m 0).toNat : ℕ) : ℝ) =
      (M : ℝ) - (max m 0 : ℝ) := by
    exact_mod_cast hcountInt
  rw [sum_finite_shifted_increments f m t M, hboundary, hcountReal]

end ProbabilityBasics

end
