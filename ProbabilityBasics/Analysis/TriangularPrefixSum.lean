/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-! Exact finite algebra for nested prefix sums and their normalized endpoint weights. -/

public section

namespace ProbabilityBasics

/-- Reordering nested prefixes gives each entry the number of later prefixes
that contain it. This is the finite identity used in JR Appendix B, Lemma B.6,
p. 43, lines 2744–2751. -/
theorem sum_range_sum_range_eq_sum_weighted (a : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, ∑ j ∈ Finset.range k, a j) =
      ∑ j ∈ Finset.range n, ((n : ℝ) - (j : ℝ) - 1) * a j := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      rw [ih]
      have hlast : ((n + 1 : ℕ) : ℝ) - (n : ℝ) - 1 = 0 := by
        simp only [Nat.cast_add, Nat.cast_one]
        ring
      rw [hlast, zero_mul, add_zero, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      simp only [Nat.cast_add, Nat.cast_one]
      ring

/-- Dividing the nested-prefix reordering by the two common factors of `n`
produces the exact endpoint weight in JR Appendix B, Lemma B.6, p. 43,
lines 2744–2751. This identity includes `n = 0`. -/
theorem normalized_prefix_sum_eq_triangular_weight (a : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, (∑ j ∈ Finset.range k, a j) / (n : ℝ)) / (n : ℝ) =
      (∑ j ∈ Finset.range n,
        (1 - ((j : ℝ) + 1) / (n : ℝ)) * a j) / (n : ℝ) := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hnreal : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    calc
      (∑ k ∈ Finset.range n, (∑ j ∈ Finset.range k, a j) / (n : ℝ)) / (n : ℝ)
          = ((∑ k ∈ Finset.range n, ∑ j ∈ Finset.range k, a j) / (n : ℝ)) / (n : ℝ) := by
              rw [← Finset.sum_div]
      _ = ((∑ j ∈ Finset.range n, ((n : ℝ) - (j : ℝ) - 1) * a j) / (n : ℝ)) /
            (n : ℝ) := by
              rw [sum_range_sum_range_eq_sum_weighted]
      _ = ∑ j ∈ Finset.range n,
            (((n : ℝ) - (j : ℝ) - 1) * a j / (n : ℝ)) / (n : ℝ) := by
              rw [← Finset.sum_div, ← Finset.sum_div]
      _ = ∑ j ∈ Finset.range n,
            ((1 - ((j : ℝ) + 1) / (n : ℝ)) * a j) / (n : ℝ) := by
              apply Finset.sum_congr rfl
              intro j _
              field_simp [hnreal]
              ring
      _ = (∑ j ∈ Finset.range n,
            (1 - ((j : ℝ) + 1) / (n : ℝ)) * a j) / (n : ℝ) := by
              rw [← Finset.sum_div]

end ProbabilityBasics
