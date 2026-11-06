/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.BilateralArray
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith

/-! Bilateral auxiliary increments of the joint array.
The natural parameter n selects the positive root r=n+1. -/

@[expose] public section

open MeasureTheory

namespace LPPDifferentiability

/-- The negative starting point corresponding to positive root n+1. -/
def bilateralIncrementRoot (n : ℕ) : ℤ := -((n + 1 : ℕ) : ℤ)

/-- Auxiliary increments, with boundary and left-extension values taken only
from proper array coordinates. No diagonal or off-domain value is assigned. -/
def bilateralArrayIncrements (n : ℕ) (x : BilateralArray) (t : ℤ) : ℝ :=
  if h : bilateralIncrementRoot n < t then
    x ⟨(bilateralIncrementRoot n, t + 1), by omega⟩ -
      x ⟨(bilateralIncrementRoot n, t), h⟩
  else if h : t = bilateralIncrementRoot n then
    x ⟨(bilateralIncrementRoot n, bilateralIncrementRoot n + 1), by omega⟩
  else
    x ⟨(t, t + 1), by omega⟩

theorem bilateralArrayIncrements_of_root_lt (n : ℕ) (x : BilateralArray)
    (t : ℤ) (h : bilateralIncrementRoot n < t) :
    bilateralArrayIncrements n x t =
      x ⟨(bilateralIncrementRoot n, t + 1), by omega⟩ -
        x ⟨(bilateralIncrementRoot n, t), h⟩ := by
  simp only [bilateralArrayIncrements, dite_eq_left h]

theorem bilateralArrayIncrements_at_root (n : ℕ) (x : BilateralArray) :
    bilateralArrayIncrements n x (bilateralIncrementRoot n) =
      x ⟨(bilateralIncrementRoot n, bilateralIncrementRoot n + 1), by omega⟩ := by
  simp only [bilateralArrayIncrements, lt_self_iff_false, ↓reduceDIte]

theorem bilateralArrayIncrements_of_lt_root (n : ℕ) (x : BilateralArray)
    (t : ℤ) (h : t < bilateralIncrementRoot n) :
    bilateralArrayIncrements n x t = x ⟨(t, t + 1), by omega⟩ := by
  rw [bilateralArrayIncrements, dite_eq_right (by omega), dite_eq_right (by omega)]

theorem continuous_bilateralArrayIncrements_coordinate (n : ℕ) (t : ℤ) :
    Continuous (fun x : BilateralArray => bilateralArrayIncrements n x t) := by
  unfold bilateralArrayIncrements
  split_ifs
  · exact (continuous_apply _).sub (continuous_apply _)
  · exact continuous_apply _
  · exact continuous_apply _

theorem measurable_bilateralArrayIncrements_coordinate (n : ℕ) (t : ℤ) :
    Measurable (fun x : BilateralArray => bilateralArrayIncrements n x t) := by
  unfold bilateralArrayIncrements
  split_ifs
  · exact (measurable_pi_apply _).sub (measurable_pi_apply _)
  · exact measurable_pi_apply _
  · exact measurable_pi_apply _

theorem continuous_bilateralArrayIncrements (n : ℕ) :
    Continuous (bilateralArrayIncrements n) :=
  continuous_pi (continuous_bilateralArrayIncrements_coordinate n)

theorem measurable_bilateralArrayIncrements (n : ℕ) :
    Measurable (bilateralArrayIncrements n) :=
  Measurable.of_eval (measurable_bilateralArrayIncrements_coordinate n)

/-- The exact shift identity, including the root and left-extension cases. -/
theorem bilateralArrayIncrements_shift (n : ℕ) (x : BilateralArray) (t : ℤ) :
    bilateralArrayIncrements (n + 1) (bilateralArrayShift x) t =
      bilateralArrayIncrements n x (t + 1) := by
  have hr : bilateralIncrementRoot (n + 1) + 1 = bilateralIncrementRoot n := by
    simp only [bilateralIncrementRoot, Nat.cast_add, Nat.cast_one]
    omega
  by_cases h : bilateralIncrementRoot (n + 1) < t
  · rw [bilateralArrayIncrements_of_root_lt _ _ _ h,
      bilateralArrayIncrements_of_root_lt _ _ _ (by omega)]
    simp only [bilateralArrayShift_apply, hr]
  · by_cases he : t = bilateralIncrementRoot (n + 1)
    · subst t
      rw [bilateralArrayIncrements_at_root]
      simpa only [bilateralArrayShift_apply, hr] using (bilateralArrayIncrements_at_root n x).symm
    · have hl : t < bilateralIncrementRoot (n + 1) := by omega
      rw [bilateralArrayIncrements_of_lt_root _ _ _ hl,
        bilateralArrayIncrements_of_lt_root _ _ _ (by omega)]
      rfl

/-- Superadditivity forces an interior increment to dominate its unit interval. -/
theorem unit_le_bilateralArrayIncrements_of_superadditive
    (x : BilateralArray)
    (hadd : ∀ (a b c : ℤ) (hab : a < b) (hbc : b < c),
      x ⟨(a, b), hab⟩ + x ⟨(b, c), hbc⟩ ≤ x ⟨(a, c), by omega⟩)
    (n : ℕ) (t : ℤ) :
    x ⟨(t, t + 1), by omega⟩ ≤ bilateralArrayIncrements n x t := by
  by_cases h : bilateralIncrementRoot n < t
  · rw [bilateralArrayIncrements_of_root_lt _ _ _ h]
    have hs := hadd (bilateralIncrementRoot n) t (t + 1) h (by omega)
    linarith only [hs]
  · by_cases he : t = bilateralIncrementRoot n
    · subst t
      rw [bilateralArrayIncrements_at_root]
    · rw [bilateralArrayIncrements_of_lt_root _ _ _ (by omega)]

/-- Conditional finite geometry for a nonnegative superadditive array. -/
theorem bilateralArrayIncrements_nonneg_of_nonneg_superadditive
    (x : BilateralArray) (hnonneg : ∀ p, 0 ≤ x p)
    (hadd : ∀ (a b c : ℤ) (hab : a < b) (hbc : b < c),
      x ⟨(a, b), hab⟩ + x ⟨(b, c), hbc⟩ ≤ x ⟨(a, c), by omega⟩)
    (n : ℕ) (t : ℤ) : 0 ≤ bilateralArrayIncrements n x t :=
  (hnonneg ⟨(t, t + 1), by omega⟩).trans
    (unit_le_bilateralArrayIncrements_of_superadditive x hadd n t)

/-- Finite telescoping strictly to the right of the chosen root. -/
theorem sum_range_bilateralArrayIncrements (n : ℕ) (x : BilateralArray)
    (a : ℤ) (ha : bilateralIncrementRoot n < a) (k : ℕ) :
    (∑ j ∈ Finset.range k, bilateralArrayIncrements n x (a + (j : ℤ))) =
      x ⟨(bilateralIncrementRoot n, a + (k : ℤ)), by omega⟩ -
        x ⟨(bilateralIncrementRoot n, a), ha⟩ := by
  induction k with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, add_zero, sub_self]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih,
      bilateralArrayIncrements_of_root_lt _ _ _ (by omega)]
    simp only [Nat.cast_add, Nat.cast_one, add_assoc]
    linarith only []

/-- The proper-interval telescoping equation; r=n+1>-a is root<a. -/
theorem sum_Ico_bilateralArrayIncrements (n : ℕ) (x : BilateralArray)
    (a b : ℤ) (hab : a < b) (ha : bilateralIncrementRoot n < a) :
    (∑ t ∈ Finset.Ico a b, bilateralArrayIncrements n x t) =
      x ⟨(bilateralIncrementRoot n, b), by omega⟩ -
        x ⟨(bilateralIncrementRoot n, a), ha⟩ := by
  rw [Int.Ico_eq_finset_map, Finset.sum_map]
  change (∑ j ∈ Finset.range (b - a).toNat,
    bilateralArrayIncrements n x (a + (j : ℤ))) = _
  have hcast : a + ((b - a).toNat : ℤ) = b := by omega
  simpa only [hcast] using sum_range_bilateralArrayIncrements n x a ha (b - a).toNat

/-- Every proper interval to the right of the root is majorized by its
increments; the only mathematical premise here is array superadditivity. -/
theorem interval_le_sum_Ico_bilateralArrayIncrements_of_superadditive
    (x : BilateralArray)
    (hadd : ∀ (a b c : ℤ) (hab : a < b) (hbc : b < c),
      x ⟨(a, b), hab⟩ + x ⟨(b, c), hbc⟩ ≤ x ⟨(a, c), by omega⟩)
    (n : ℕ) (a b : ℤ) (hab : a < b) (ha : bilateralIncrementRoot n < a) :
    x ⟨(a, b), hab⟩ ≤ ∑ t ∈ Finset.Ico a b, bilateralArrayIncrements n x t := by
  rw [sum_Ico_bilateralArrayIncrements n x a b hab ha]
  have hs := hadd (bilateralIncrementRoot n) a b ha hab
  linarith only [hs]

end LPPDifferentiability
