/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.CesaroLaw
public import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Coordinate averages for the sequence shift

Finite-sum identities used in Liggett's stationary block argument. The empty
average is the Birkhoff average at zero.
-/

public section

namespace LPPDifferentiability

/-- Iterating the literal shift evaluates the corresponding later coordinate. -/
theorem sequenceShift_iterate_apply (z : ℕ → ℝ) (n k : ℕ) :
    ((sequenceShift^[n]) z) k = z (k + n) := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change ((sequenceShift^[n]) z) (k + 1) = z (k + (n + 1))
    rw [ih]
    congr 1
    omega

/-- The canonical coordinate Birkhoff average is the actual finite sequence sum. -/
theorem birkhoffAverage_sequenceShift_eval_zero (z : ℕ → ℝ) (n : ℕ) :
    birkhoffAverage ℝ sequenceShift (fun x : ℕ → ℝ => x 0) n z =
      (∑ i ∈ Finset.range n, z i) / (n : ℝ) := by
  simp only [birkhoffAverage, birkhoffSum, sequenceShift_iterate_apply,
    Nat.zero_add, smul_eq_mul, div_eq_inv_mul]

/-- Separate the first value from the average of the shifted tail. This holds
at zero as well, where the tail average is empty. -/
theorem birkhoffAverage_sequenceShift_succ (z : ℕ → ℝ) (n : ℕ) :
    birkhoffAverage ℝ sequenceShift (fun x : ℕ → ℝ => x 0) (n + 1) z =
      (n : ℝ) / (n + 1 : ℝ) *
        birkhoffAverage ℝ sequenceShift (fun x : ℕ → ℝ => x 0) n (sequenceShift z) +
      z 0 / (n + 1 : ℝ) := by
  rw [birkhoffAverage_sequenceShift_eval_zero, birkhoffAverage_sequenceShift_eval_zero,
    Finset.sum_range_succ']
  simp only [sequenceShift, Nat.cast_add, Nat.cast_one]
  by_cases hn : n = 0
  · subst n
    simp
  · have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
    field_simp [hn', hn1]

end LPPDifferentiability
