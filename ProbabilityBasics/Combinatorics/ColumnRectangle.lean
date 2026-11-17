/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Interval
import Mathlib.Tactic

/-! Finite normalization for a column in an integer-lattice rectangle. -/

@[expose] public section

open scoped BigOperators

namespace ProbabilityBasics

/-- Summing a function of the first coordinate over an integer column repeats each value `n` times. -/
theorem sum_column_rectangle_div_sq (g : ℤ → ℝ) (N n : ℕ) :
    (∑ z ∈ (Finset.Ico (0 : ℤ) (N : ℤ)).product
        (Finset.Ico (0 : ℤ) (n : ℤ)), g z.1) / (n : ℝ)^2 =
      (∑ j ∈ Finset.Ico (0 : ℤ) (N : ℤ), g j) / (n : ℝ) := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    let s : Finset ℤ := Finset.Ico 0 (N : ℤ)
    let t : Finset ℤ := Finset.Ico 0 (n : ℤ)
    have hcard : (t.card : ℝ) = (n : ℝ) := by
      have hcardZ : (t.card : ℤ) = (n : ℤ) := by
        simp [t]
      exact_mod_cast hcardZ
    have hsum : (∑ z ∈ s.product t, g z.1) =
        (n : ℝ) * ∑ j ∈ s, g j := by
      calc
        _ = ∑ j ∈ s, ∑ k ∈ t, g j := by
          exact Finset.sum_product s t (fun z : ℤ × ℤ => g z.1)
        _ = ∑ j ∈ s, (n : ℝ) * g j := by
          apply Finset.sum_congr rfl
          intro j hj
          simp only [Finset.sum_const, nsmul_eq_mul, hcard]
        _ = (n : ℝ) * ∑ j ∈ s, g j := by rw [Finset.mul_sum]
    calc
      (∑ z ∈ (Finset.Ico (0 : ℤ) (N : ℤ)).product
          (Finset.Ico (0 : ℤ) (n : ℤ)), g z.1) / (n : ℝ)^2 =
          ((n : ℝ) * ∑ j ∈ s, g j) / (n : ℝ)^2 := by
            simpa only [s, t] using congrArg (fun x : ℝ => x / (n : ℝ)^2) hsum
      _ = (∑ j ∈ Finset.Ico (0 : ℤ) (N : ℤ), g j) / (n : ℝ) := by
        dsimp only [s]
        field_simp [hnR]

end ProbabilityBasics
