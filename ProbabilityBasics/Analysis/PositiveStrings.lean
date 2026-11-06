/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-! # Finite positive strings

The deterministic string argument in Keane–Petersen, arXiv:math/0608251v1,
pp. 248–249. A completed positive string contributes nonnegatively after
masking; an unfinished string costs at most the horizon times the lower bound.
-/

public section

open Finset

namespace LPPDifferentiability

/-- A positive string of length between one and `N` starts at `i`. -/
@[expose] def positive_string (a : ℕ → ℝ) (N i : ℕ) : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ k ≤ N ∧ 0 < ∑ j ∈ range k, a (i + j)

/-- Keep the sequence value exactly at starts of positive strings. -/
@[expose] noncomputable def positiveStringTerm (a : ℕ → ℝ) (N i : ℕ) : ℝ := by
  classical
  exact if positive_string a N i then a i else 0

/-- The length-one test ensures that masking can only increase a value. -/
theorem le_positiveStringTerm (a : ℕ → ℝ) (N : ℕ) (hN : 1 ≤ N) (i : ℕ) :
    a i ≤ positiveStringTerm a N i := by
  classical
  unfold positiveStringTerm
  split_ifs with h
  · exact le_rfl
  · by_contra hn
    apply h
    refine ⟨1, le_rfl, hN, ?_⟩
    simpa only [sum_range_one, Nat.add_zero] using (lt_of_not_ge hn)

/-- The masked sequence inherits any nonpositive constant lower bound. -/
theorem neg_le_positiveStringTerm (a : ℕ → ℝ) (N : ℕ) (C : ℝ)
    (hC : 0 ≤ C) (ha : ∀ i, -C ≤ a i) (i : ℕ) :
    -C ≤ positiveStringTerm a N i := by
  classical
  unfold positiveStringTerm
  split_ifs
  · exact ha i
  · exact neg_nonpos.mpr hC

/-- Every finite segment of the masked sequence is bounded below by `-N*C`.
The start is arbitrary so that complete positive blocks can be removed by
strong induction on the remaining segment length. -/
theorem neg_mul_le_sum_positiveStringTerm (a : ℕ → ℝ) (N : ℕ) (hN : 1 ≤ N)
    (C : ℝ) (hC : 0 ≤ C) (ha : ∀ i, -C ≤ a i) (m s : ℕ) :
    -(N : ℝ) * C ≤ ∑ i ∈ range m, positiveStringTerm a N (s + i) := by
  classical
  induction m using Nat.strong_induction_on generalizing s with
  | h m ih =>
    by_cases hm : m = 0
    · subst m
      simpa only [range_zero, sum_empty] using (mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (Nat.cast_nonneg N)) hC)
    by_cases hs : positive_string a N s
    · obtain ⟨k, hk, hkN, hpos⟩ := hs
      by_cases hkm : k ≤ m
      · have hblock : 0 ≤ ∑ i ∈ range k, positiveStringTerm a N (s + i) :=
          le_trans (le_of_lt hpos) (sum_le_sum fun i _ ↦ le_positiveStringTerm a N hN (s + i))
        have htail := ih (m - k) (by omega) (s + k)
        have hsplit : m = k + (m - k) := by omega
        rw [hsplit, sum_range_add]
        have htail' : -(N : ℝ) * C ≤
            ∑ i ∈ range (m - k), positiveStringTerm a N (s + (k + i)) := by
          simpa only [Nat.add_assoc] using htail
        exact le_trans htail' (le_add_of_nonneg_left hblock)
      · have hmN : (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show m ≤ N by omega)
        calc
          -(N : ℝ) * C ≤ -(m : ℝ) * C :=
            mul_le_mul_of_nonneg_right (neg_le_neg hmN) hC
          _ = ∑ _i ∈ range m, -C := by
            simp only [sum_const, card_range, nsmul_eq_mul, mul_neg, neg_mul]
          _ ≤ _ := sum_le_sum fun i _ ↦ neg_le_positiveStringTerm a N C hC ha (s + i)
    · have hfirst : positiveStringTerm a N s = 0 := by
        simp only [positiveStringTerm, ite_eq_right hs]
      obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
      rw [sum_range_succ']
      simpa only [Nat.add_zero, hfirst, add_zero, Nat.add_assoc, Nat.add_comm 1]
        using ih r (Nat.lt_succ_self r) (s + 1)

end LPPDifferentiability
