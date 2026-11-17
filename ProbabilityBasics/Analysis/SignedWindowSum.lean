/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
import ProbabilityBasics.Probability.UniformIncrementShift

/-!
# Bounded signed-window sums

A bounded real sequence changes a finite window sum by at most two boundary
terms for each unit of integer shift.
-/

public section

namespace ProbabilityBasics

/-- A bounded real sequence changes a finite window sum by at most two bounds
for each unit of integer shift. The one-step cancellation is
`LPPDifferentiability.sum_shift_sub` in
`ProbabilityBasics/Probability/UniformIncrementShift.lean:37-43`. -/
theorem norm_sum_int_shift_sub_le (a : ℤ → ℝ) (C : ℝ)
    (hC : ∀ k, ‖a k‖ ≤ C) (m : ℤ) (N : ℕ) :
    ‖(∑ k : Fin N, a ((k.val : ℤ) + m)) -
      (∑ k : Fin N, a (k.val : ℤ))‖ ≤ 2 * C * (m.natAbs : ℝ) := by
  let W : ℤ → ℝ := fun t => ∑ u : Fin N, a (t + u.val)
  -- One shift changes the window only at its two endpoints.
  have hstep (t : ℤ) : ‖W (t + 1) - W t‖ ≤ 2 * C := by
    have hsum : W (t + 1) - W t = a (t + (N : ℤ)) - a t := by
      convert LPPDifferentiability.sum_shift_sub (fun j : ℕ => a (t + j)) N using 1 <;>
        simp only [W, Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero, add_assoc,
          add_comm (1 : ℤ)]
    rw [hsum]
    have hleft := hC (t + (N : ℤ))
    have hright := hC t
    exact (norm_sub_le _ _).trans (by
      calc
        ‖a (t + (N : ℤ))‖ + ‖a t‖ ≤ C + C := add_le_add hleft hright
        _ = 2 * C := by ring)
  -- A nonnegative integer shift accumulates one endpoint bound at each step.
  have hpos (q : ℕ) (t : ℤ) :
      ‖W (t + q) - W t‖ ≤ 2 * C * (q : ℝ) := by
    induction q with
    | zero =>
      simp only [Nat.cast_zero, add_zero, sub_self, norm_zero, mul_zero, le_refl]
    | succ q ih =>
      have hsplit : W (t + (q + 1 : ℕ)) - W t =
          (W (t + q + 1) - W (t + q)) + (W (t + q) - W t) := by
        rw [Nat.cast_add, Nat.cast_one, ← add_assoc]
        ring
      rw [hsplit]
      calc
        ‖(W (t + q + 1) - W (t + q)) + (W (t + q) - W t)‖ ≤
            ‖W (t + q + 1) - W (t + q)‖ + ‖W (t + q) - W t‖ := norm_add_le _ _
        _ ≤ 2 * C + 2 * C * (q : ℝ) := add_le_add (hstep (t + q)) ih
        _ = 2 * C * ((q + 1 : ℕ) : ℝ) := by push_cast; ring
  -- The integer cases reduce to positive shifts or their reversals.
  have hbound : ‖W m - W 0‖ ≤ 2 * C * (m.natAbs : ℝ) := by
    cases m with
    | ofNat q =>
      simpa only [Int.ofNat_eq_natCast, Int.natAbs_natCast, zero_add] using hpos q 0
    | negSucc q =>
      have h := hpos (q + 1) (Int.negSucc q)
      have hzero : Int.negSucc q + ((q + 1 : ℕ) : ℤ) = 0 := by omega
      rw [hzero, norm_sub_rev] at h
      simpa only [Int.natAbs_negSucc] using h
  simpa only [W, add_zero, add_comm] using hbound

end ProbabilityBasics
