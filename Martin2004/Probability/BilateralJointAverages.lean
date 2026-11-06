/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.BilateralJointShift
public import Martin2004.Probability.BirkhoffRateIdentification
import Mathlib.Tactic.NormNum

/-! # Finite averages on the bilateral joint shift

The actual joint shift and the existing Birkhoff averages have literal integer
coordinate formulas. These are pointwise identities and require no probability
or stationarity assumptions.
-/

public section

namespace LPPDifferentiability

/-- The second-coordinate evaluation of the actual joint shift. -/
theorem bilateralJointShiftMeasurableEquiv_snd_apply
    (p : BilateralJoint) (t : ℤ) :
    (bilateralJointShiftMeasurableEquiv p).2 t = p.2 (t + 1) := rfl

/-- The second-coordinate evaluation of the actual inverse joint shift. -/
theorem bilateralJointShiftMeasurableEquiv_symm_snd_apply
    (p : BilateralJoint) (t : ℤ) :
    (bilateralJointShiftMeasurableEquiv.symm p).2 t = p.2 (t - 1) := rfl

/-- Forward iterates of the actual joint shift move the increment coordinate
from `t` to `t + n`.
-/
theorem bilateralJointShiftMeasurableEquiv_iterate_snd_apply
    (p : BilateralJoint) (n : ℕ) (t : ℤ) :
    (((bilateralJointShiftMeasurableEquiv : BilateralJoint → BilateralJoint)^[n]) p).2 t =
      p.2 (t + (n : ℤ)) := by
  induction n generalizing t with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', bilateralJointShiftMeasurableEquiv_snd_apply]
    rw [ih]
    apply congrArg (p.2)
    push_cast
    omega

/-- Inverse iterates of the actual joint shift move the increment coordinate
from `t` to `t - n`.
-/
theorem bilateralJointShiftMeasurableEquiv_symm_iterate_snd_apply
    (p : BilateralJoint) (n : ℕ) (t : ℤ) :
    (((bilateralJointShiftMeasurableEquiv.symm : BilateralJoint → BilateralJoint)^[n]) p).2 t =
      p.2 (t - (n : ℤ)) := by
  induction n generalizing t with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', bilateralJointShiftMeasurableEquiv_symm_snd_apply]
    rw [ih]
    apply congrArg (p.2)
    push_cast
    omega

/-- The actual forward Birkhoff average of the second-coordinate observable is
the sum of `z(0), ..., z(n-1)`, divided by `n`.
-/
theorem birkhoffAverage_bilateralJointShift_snd_zero_eq_sum
    (p : BilateralJoint) (n : ℕ) :
    birkhoffAverage ℝ bilateralJointShiftMeasurableEquiv
      (fun p : BilateralJoint => p.2 0) n p =
        (∑ j ∈ Finset.range n, p.2 (j : ℤ)) / (n : ℝ) := by
  simp only [birkhoffAverage, birkhoffSum,
    bilateralJointShiftMeasurableEquiv_iterate_snd_apply, zero_add,
    smul_eq_mul, div_eq_inv_mul]

/-- The existing backward Birkhoff average is exactly the sum of
`z(-1), ..., z(-n)`, divided by `n`.
-/
theorem backwardBirkhoffAverage_bilateralJointShift_snd_zero_eq_sum
    (p : BilateralJoint) (n : ℕ) :
    backwardBirkhoffAverage bilateralJointShiftMeasurableEquiv
      (fun p : BilateralJoint => p.2 0) n p =
        (∑ j ∈ Finset.range n, p.2 (-((j : ℤ) + 1))) / (n : ℝ) := by
  rw [backwardBirkhoffAverage_eq_sum]
  simp only [bilateralJointShiftMeasurableEquiv_symm_iterate_snd_apply,
    Nat.cast_add, Nat.cast_one, zero_sub, div_eq_inv_mul]

private theorem sum_range_negative_bilateral (z : ℤ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, z (-(n : ℤ) + (i : ℤ))) =
      ∑ j ∈ Finset.range n, z (-((j : ℤ) + 1)) := by
  rw [← Finset.sum_range_reflect (fun j : ℕ => z (-((j : ℤ) + 1))) n]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < n := Finset.mem_range.mp hi
  congr 1
  omega

/-- Split the literal centered integer window into its negative and
nonnegative coordinates. The interval contains exactly `2n` terms, including
the empty window when `n = 0`.
-/
private theorem sum_Ico_bilateral_eq_negative_add_nonnegative
    (z : ℤ → ℝ) (n : ℕ) :
    (∑ t ∈ Finset.Ico (-(n : ℤ)) (n : ℤ), z t) =
      (∑ j ∈ Finset.range n, z (-((j : ℤ) + 1))) +
        ∑ j ∈ Finset.range n, z (j : ℤ) := by
  rw [Int.Ico_eq_finset_map, Finset.sum_map]
  have hlen : ((n : ℤ) - (-(n : ℤ))).toNat = 2 * n := by omega
  rw [hlen]
  change (∑ i ∈ Finset.range (2 * n), z (-(n : ℤ) + (i : ℤ))) = _
  rw [show 2 * n = n + n by omega, Finset.sum_range_add,
    sum_range_negative_bilateral]
  simp only [Nat.cast_add, neg_add_cancel_left]

/-- The actual centered Birkhoff average sums precisely the `2n` coordinates
in `[-n,n)`, with no endpoint correction and with the empty average at zero.
-/
theorem centeredBirkhoffAverage_bilateralJointShift_snd_zero_eq_sum
    (p : BilateralJoint) (n : ℕ) :
    centeredBirkhoffAverage bilateralJointShiftMeasurableEquiv
      (fun p : BilateralJoint => p.2 0) n p =
        (∑ t ∈ Finset.Ico (-(n : ℤ)) (n : ℤ), p.2 t) / (2 * (n : ℝ)) := by
  rw [centeredBirkhoffAverage,
    birkhoffAverage_bilateralJointShift_snd_zero_eq_sum,
    backwardBirkhoffAverage_bilateralJointShift_snd_zero_eq_sum,
    ← add_div, div_div, sum_Ico_bilateral_eq_negative_add_nonnegative]
  rw [mul_comm, add_comm]

private def signedSequenceExample : BilateralJoint := (0, fun t : ℤ => (t : ℝ))

private def constantNegativeThreeExample : BilateralJoint := (0, fun _ : ℤ => -3)

/-- The signed nonconstant sequence `z(t)=t` checks zero, first, and third
forward, backward, and centered averages, including both endpoint conventions.
-/
private theorem signedSequence_bilateralAverage_examples :
    birkhoffAverage ℝ bilateralJointShiftMeasurableEquiv
        (fun p : BilateralJoint => p.2 0) 0 signedSequenceExample = 0 ∧
      birkhoffAverage ℝ bilateralJointShiftMeasurableEquiv
        (fun p : BilateralJoint => p.2 0) 1 signedSequenceExample = 0 ∧
      birkhoffAverage ℝ bilateralJointShiftMeasurableEquiv
        (fun p : BilateralJoint => p.2 0) 3 signedSequenceExample = 1 ∧
      backwardBirkhoffAverage bilateralJointShiftMeasurableEquiv
        (fun p : BilateralJoint => p.2 0) 0 signedSequenceExample = 0 ∧
      backwardBirkhoffAverage bilateralJointShiftMeasurableEquiv
        (fun p : BilateralJoint => p.2 0) 1 signedSequenceExample = -1 ∧
      backwardBirkhoffAverage bilateralJointShiftMeasurableEquiv
        (fun p : BilateralJoint => p.2 0) 3 signedSequenceExample = -2 ∧
      centeredBirkhoffAverage bilateralJointShiftMeasurableEquiv
        (fun p : BilateralJoint => p.2 0) 0 signedSequenceExample = 0 ∧
      centeredBirkhoffAverage bilateralJointShiftMeasurableEquiv
        (fun p : BilateralJoint => p.2 0) 1 signedSequenceExample = -(1 / 2 : ℝ) ∧
      centeredBirkhoffAverage bilateralJointShiftMeasurableEquiv
        (fun p : BilateralJoint => p.2 0) 3 signedSequenceExample = -(1 / 2 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [birkhoffAverage_bilateralJointShift_snd_zero_eq_sum]
    norm_num [signedSequenceExample, Finset.sum_range_succ]
  · rw [birkhoffAverage_bilateralJointShift_snd_zero_eq_sum]
    norm_num [signedSequenceExample, Finset.sum_range_succ]
  · rw [birkhoffAverage_bilateralJointShift_snd_zero_eq_sum]
    norm_num [signedSequenceExample, Finset.sum_range_succ]
  · rw [backwardBirkhoffAverage_bilateralJointShift_snd_zero_eq_sum]
    norm_num [signedSequenceExample, Finset.sum_range_succ]
  · rw [backwardBirkhoffAverage_bilateralJointShift_snd_zero_eq_sum]
    norm_num [signedSequenceExample, Finset.sum_range_succ]
  · rw [backwardBirkhoffAverage_bilateralJointShift_snd_zero_eq_sum]
    norm_num [signedSequenceExample, Finset.sum_range_succ]
  · rw [centeredBirkhoffAverage_bilateralJointShift_snd_zero_eq_sum,
      sum_Ico_bilateral_eq_negative_add_nonnegative]
    norm_num [signedSequenceExample, Finset.sum_range_succ]
  · rw [centeredBirkhoffAverage_bilateralJointShift_snd_zero_eq_sum,
      sum_Ico_bilateral_eq_negative_add_nonnegative]
    norm_num [signedSequenceExample, Finset.sum_range_succ]
  · rw [centeredBirkhoffAverage_bilateralJointShift_snd_zero_eq_sum,
      sum_Ico_bilateral_eq_negative_add_nonnegative]
    norm_num [signedSequenceExample, Finset.sum_range_succ]

/-- The constant sequence `z(t)=-3` checks the same three average conventions;
the empty average remains zero.
-/
private theorem constantNegativeThree_bilateralAverage_examples :
    birkhoffAverage ℝ bilateralJointShiftMeasurableEquiv
        (fun p : BilateralJoint => p.2 0) 0 constantNegativeThreeExample = 0 ∧
      birkhoffAverage ℝ bilateralJointShiftMeasurableEquiv
        (fun p : BilateralJoint => p.2 0) 1 constantNegativeThreeExample = -3 ∧
      birkhoffAverage ℝ bilateralJointShiftMeasurableEquiv
        (fun p : BilateralJoint => p.2 0) 3 constantNegativeThreeExample = -3 ∧
      backwardBirkhoffAverage bilateralJointShiftMeasurableEquiv
        (fun p : BilateralJoint => p.2 0) 0 constantNegativeThreeExample = 0 ∧
      backwardBirkhoffAverage bilateralJointShiftMeasurableEquiv
        (fun p : BilateralJoint => p.2 0) 1 constantNegativeThreeExample = -3 ∧
      backwardBirkhoffAverage bilateralJointShiftMeasurableEquiv
        (fun p : BilateralJoint => p.2 0) 3 constantNegativeThreeExample = -3 ∧
      centeredBirkhoffAverage bilateralJointShiftMeasurableEquiv
        (fun p : BilateralJoint => p.2 0) 0 constantNegativeThreeExample = 0 ∧
      centeredBirkhoffAverage bilateralJointShiftMeasurableEquiv
        (fun p : BilateralJoint => p.2 0) 1 constantNegativeThreeExample = -3 ∧
      centeredBirkhoffAverage bilateralJointShiftMeasurableEquiv
        (fun p : BilateralJoint => p.2 0) 3 constantNegativeThreeExample = -3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [birkhoffAverage_bilateralJointShift_snd_zero_eq_sum]
    norm_num [constantNegativeThreeExample, Finset.sum_range_succ]
  · rw [birkhoffAverage_bilateralJointShift_snd_zero_eq_sum]
    norm_num [constantNegativeThreeExample, Finset.sum_range_succ]
  · rw [birkhoffAverage_bilateralJointShift_snd_zero_eq_sum]
    norm_num [constantNegativeThreeExample, Finset.sum_range_succ]
  · rw [backwardBirkhoffAverage_bilateralJointShift_snd_zero_eq_sum]
    norm_num [constantNegativeThreeExample, Finset.sum_range_succ]
  · rw [backwardBirkhoffAverage_bilateralJointShift_snd_zero_eq_sum]
    norm_num [constantNegativeThreeExample, Finset.sum_range_succ]
  · rw [backwardBirkhoffAverage_bilateralJointShift_snd_zero_eq_sum]
    norm_num [constantNegativeThreeExample, Finset.sum_range_succ]
  · rw [centeredBirkhoffAverage_bilateralJointShift_snd_zero_eq_sum,
      sum_Ico_bilateral_eq_negative_add_nonnegative]
    norm_num [constantNegativeThreeExample, Finset.sum_range_succ]
  · rw [centeredBirkhoffAverage_bilateralJointShift_snd_zero_eq_sum,
      sum_Ico_bilateral_eq_negative_add_nonnegative]
    norm_num [constantNegativeThreeExample, Finset.sum_range_succ]
  · rw [centeredBirkhoffAverage_bilateralJointShift_snd_zero_eq_sum,
      sum_Ico_bilateral_eq_negative_add_nonnegative]
    norm_num [constantNegativeThreeExample, Finset.sum_range_succ]

end LPPDifferentiability
