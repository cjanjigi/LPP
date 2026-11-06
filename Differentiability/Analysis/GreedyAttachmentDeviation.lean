/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Greedy attachment deviation bounds

Scalar bounds for the two preferred choices and the actual finite
preferred-versus-forced recurrence used in the attachment construction.
-/

public section

namespace LPPDifferentiability

/-- At a middle slope, one of the two next deviations is within the source
bound. -/
theorem greedy_attachment_preferred_step_abs_le
    (d c : ℝ) (hc_lo : 1 / 4 ≤ c) (hc_hi : c ≤ 3 / 4) :
    min |d + c| |d + c - 1| ≤ max 1 (|d| - 1 / 4) := by
  by_cases hd_pos : 1 < d
  · have hd : 0 < d := by linarith
    have hq : 0 < d + c - 1 := by linarith
    have hq_le : d + c - 1 ≤ d - 1 / 4 := by linarith
    have hq_abs : |d + c - 1| ≤ |d| - 1 / 4 := by
      rw [abs_of_pos hq, abs_of_pos hd]
      exact hq_le
    exact (min_le_right _ _).trans
      (hq_abs.trans (le_max_right 1 (|d| - 1 / 4)))
  · by_cases hd_neg : d < -1
    · have hp : d + c < 0 := by linarith
      have hd : d < 0 := by linarith
      have hp_abs : |d + c| ≤ |d| - 1 / 4 := by
        rw [abs_of_neg hp, abs_of_neg hd]
        linarith
      exact (min_le_left _ _).trans
        (hp_abs.trans (le_max_right 1 (|d| - 1 / 4)))
    · have hd_lo : -1 ≤ d := le_of_not_gt hd_neg
      have hd_hi : d ≤ 1 := le_of_not_gt hd_pos
      have hp_lo : -3 / 4 ≤ d + c := by linarith
      have hp_hi : d + c ≤ 7 / 4 := by linarith
      by_cases hp_nonpos : d + c ≤ 0
      · have hp_abs : |d + c| ≤ 1 := by
          rw [abs_of_nonpos hp_nonpos]
          linarith
        exact (min_le_left _ _).trans (hp_abs.trans (le_max_left _ _))
      · have hp_pos : 0 < d + c := lt_of_not_ge hp_nonpos
        by_cases hp_le_one : d + c ≤ 1
        · have hp_abs : |d + c| ≤ 1 := by
            rw [abs_of_nonneg hp_pos.le]
            exact hp_le_one
          exact (min_le_left _ _).trans (hp_abs.trans (le_max_left _ _))
        · have hq_pos : 0 < d + c - 1 := by linarith
          have hq_abs : |d + c - 1| ≤ 1 := by
            rw [abs_of_nonneg hq_pos.le]
            linarith
          exact (min_le_right _ _).trans (hq_abs.trans (le_max_left _ _))

/-- A finite sequence following the preferred-or-forced rule
has deviation at most one plus the number of forced steps. The comparison
chooses the first of two tied options; either tie choice satisfies the scalar
bound. -/
theorem greedy_attachment_deviation_bound_of_recurrence
    (c : ℝ) (hc_lo : 1 / 4 ≤ c) (hc_hi : c ≤ 3 / 4)
    (forced : ℕ → Prop) [DecidablePred forced]
    (d : ℕ → ℝ) (f : ℕ → ℕ)
    (hd_zero : d 0 = 0) (hf_zero : f 0 = 0)
    (hd_step : ∀ i, d (i + 1) =
      if |d i + c| ≤ |d i + c - 1| then
        if forced i then d i + c - 1 else d i + c
      else
        if forced i then d i + c else d i + c - 1)
    (hf_step : ∀ i, f (i + 1) = f i + if forced i then 1 else 0) :
    ∀ i, |d i| ≤ 1 + (f i : ℝ) := by
  intro i
  induction i with
  | zero =>
      rw [hd_zero, hf_zero]
      norm_num
  | succ i ih =>
      have hmax : max 1 (|d i| - 1 / 4) ≤ 1 + (f i : ℝ) := by
        apply max_le
        · have hf_nonneg : 0 ≤ (f i : ℝ) := Nat.cast_nonneg _
          linarith
        · linarith
      have hpreferred :
          |if |d i + c| ≤ |d i + c - 1| then d i + c else d i + c - 1|
            ≤ 1 + (f i : ℝ) := by
        have hselected :
            |if |d i + c| ≤ |d i + c - 1| then d i + c else d i + c - 1|
              ≤ max 1 (|d i| - 1 / 4) := by
          by_cases hchoose : |d i + c| ≤ |d i + c - 1|
          · simp only [ite_eq_left hchoose]
            have hscalar := greedy_attachment_preferred_step_abs_le (d i) c hc_lo hc_hi
            rw [min_eq_left hchoose] at hscalar
            exact hscalar
          · simp only [ite_eq_right hchoose]
            have hother_le : |d i + c - 1| ≤ |d i + c| :=
              le_of_lt (lt_of_not_ge hchoose)
            have hscalar := greedy_attachment_preferred_step_abs_le (d i) c hc_lo hc_hi
            rw [min_eq_right hother_le] at hscalar
            exact hscalar
        exact hselected.trans hmax
      rw [hd_step i, hf_step i]
      by_cases hchoose : |d i + c| ≤ |d i + c - 1|
      · by_cases hforced : forced i
        · simp only [ite_eq_left hchoose, ite_eq_left hforced, Nat.cast_add, Nat.cast_one]
          have hbound : |d i + c| ≤ 1 + (f i : ℝ) := by
            simpa [hchoose] using hpreferred
          have hother : |d i + c - 1| ≤ |d i + c| + 1 := by
            simpa using abs_sub (d i + c) 1
          linarith
        · simp only [ite_eq_left hchoose, ite_eq_right hforced, Nat.cast_add, Nat.cast_zero]
          simpa [hchoose] using hpreferred
      · by_cases hforced : forced i
        · simp only [ite_eq_right hchoose, ite_eq_left hforced, Nat.cast_add, Nat.cast_one]
          have hbound : |d i + c - 1| ≤ 1 + (f i : ℝ) := by
            simpa [hchoose] using hpreferred
          have hother : |d i + c| ≤ |d i + c - 1| + 1 := by
            calc
              |d i + c| = |(d i + c - 1) + 1| := by congr 1; ring
              _ ≤ |d i + c - 1| + |1| := abs_add_le _ _
              _ = |d i + c - 1| + 1 := by simp
          linarith
        · simp only [ite_eq_right hchoose, ite_eq_right hforced, Nat.cast_add, Nat.cast_zero]
          simpa [hchoose] using hpreferred

end LPPDifferentiability

end
