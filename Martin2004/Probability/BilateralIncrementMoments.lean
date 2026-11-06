/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.BilateralArrayIncrements
public import ProbabilityBasics.Probability.UniformOrigin
public import ProbabilityBasics.Analysis.BilateralIncrementMeanLimits
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Tactic.Ring

/-! Actual coordinate integrability and means in the bilateral
random-root construction. All array coordinates have strictly ordered endpoints. -/

@[expose] public section

open MeasureTheory Filter Topology

namespace LPPDifferentiability

/-- The literal increments are integrable on every integer coordinate. -/
theorem integrable_bilateralArrayIncrements
    (ρ : ProbabilityMeasure BilateralArray)
    (hi : ∀ p : BilateralInterval, Integrable (fun x : BilateralArray => x p) (ρ : Measure _))
    (n : ℕ) (t : ℤ) :
    Integrable (fun x => bilateralArrayIncrements n x t) (ρ : Measure _) := by
  unfold bilateralArrayIncrements
  split_ifs
  · exact (hi _).sub (hi _)
  · exact hi _
  · exact hi _

/-- Integrability under the existing independent finite-root sampler. -/
theorem integrable_uniform_bilateralArrayIncrements
    (ρ : ProbabilityMeasure BilateralArray)
    (hi : ∀ p : BilateralInterval, Integrable (fun x : BilateralArray => x p) (ρ : Measure _))
    (N : ℕ) (t : ℤ) :
    Integrable (fun p : BilateralArray × Fin (N + 1) =>
      bilateralArrayIncrements p.2.val p.1 t) (uniformOriginProduct (ρ : Measure _) N) := by
  exact integrable_uniformOrigin_family (ρ : Measure _) N
    (fun u x => bilateralArrayIncrements u.val x t)
    (fun u => measurable_bilateralArrayIncrements_coordinate u.val t)
    (fun u => integrable_bilateralArrayIncrements ρ hi u.val t)

/-- Measure preservation translates the expectation of an actual interval. -/
theorem integral_bilateralArray_coordinate_add_one
    (ρ : ProbabilityMeasure BilateralArray)
    (hS : MeasurePreserving bilateralArrayShift (ρ : Measure _) (ρ : Measure _))
    (a b : ℤ) (hab : a < b) :
    (∫ x : BilateralArray, x ⟨(a + 1, b + 1), by omega⟩ ∂(ρ : Measure _)) =
      ∫ x : BilateralArray, x ⟨(a, b), hab⟩ ∂(ρ : Measure _) := by
  exact hS.integral_comp bilateralArrayShiftHomeomorph.toMeasurableEquiv.measurableEmbedding
    (fun x : BilateralArray => x ⟨(a, b), hab⟩)

/-- Integer translation of proper intervals does not change their means. -/
theorem integral_bilateralArray_coordinate_translate
    (ρ : ProbabilityMeasure BilateralArray)
    (hS : MeasurePreserving bilateralArrayShift (ρ : Measure _) (ρ : Measure _))
    (a b k : ℤ) (hab : a < b) :
    (∫ x : BilateralArray, x ⟨(a + k, b + k), by omega⟩ ∂(ρ : Measure _)) =
      ∫ x : BilateralArray, x ⟨(a, b), hab⟩ ∂(ρ : Measure _) := by
  induction k using Int.induction_on with
  | zero => simp only [add_zero]
  | succ k ih =>
      simpa only [add_assoc] using
        (integral_bilateralArray_coordinate_add_one ρ hS (a + k) (b + k) (by omega)).trans ih
  | pred k ih =>
      have he := integral_bilateralArray_coordinate_add_one ρ hS
        (a + (-(k : ℤ) - 1)) (b + (-(k : ℤ) - 1)) (by omega)
      have ha : a + (-(k : ℤ) - 1) + 1 = a - k := by omega
      have hb : b + (-(k : ℤ) - 1) + 1 = b - k := by omega
      simp only [ha, hb] at he
      simp only [sub_eq_add_neg] at he
      exact he.symm.trans ih

/-- An interval of positive length n+1 has the corresponding actual origin mean. -/
theorem integral_bilateralArray_coordinate_eq_origin
    (ρ : ProbabilityMeasure BilateralArray)
    (hS : MeasurePreserving bilateralArrayShift (ρ : Measure _) (ρ : Measure _))
    (a : ℤ) (n : ℕ) :
    (∫ x : BilateralArray, x ⟨(a, a + ((n + 1 : ℕ) : ℤ)), by omega⟩ ∂(ρ : Measure _)) =
      (∫ x : BilateralArray, x ⟨(0, (((n) + 1 : ℕ) : ℤ)), by omega⟩ ∂(ρ : Measure _)) := by
  simpa only [add_comm, add_zero] using
    integral_bilateralArray_coordinate_translate ρ hS 0 ((n + 1 : ℕ) : ℤ) a (by omega)

/-- The expectation to the right of a root is a difference of positive-length means. -/
theorem integral_bilateralArrayIncrements_of_root_lt
    (ρ : ProbabilityMeasure BilateralArray)
    (hS : MeasurePreserving bilateralArrayShift (ρ : Measure _) (ρ : Measure _))
    (hi : ∀ p : BilateralInterval, Integrable (fun x : BilateralArray => x p) (ρ : Measure _))
    (n : ℕ) (t : ℤ) (ht : bilateralIncrementRoot n < t) :
    (∫ x, bilateralArrayIncrements n x t ∂(ρ : Measure _)) =
      (∫ x : BilateralArray, x ⟨(0, ((((t - bilateralIncrementRoot n).toNat) + 1 : ℕ) : ℤ)), by omega⟩ ∂(ρ : Measure _)) -
        (∫ x : BilateralArray, x ⟨(0, (((((t - bilateralIncrementRoot n).toNat - 1)) + 1 : ℕ) : ℤ)), by omega⟩ ∂(ρ : Measure _)) := by
  simp_rw [bilateralArrayIncrements_of_root_lt n _ t ht]
  rw [integral_sub (hi _) (hi _)]
  have h₁ : bilateralIncrementRoot n +
      (((t - bilateralIncrementRoot n).toNat + 1 : ℕ) : ℤ) = t + 1 := by omega
  have h₂ : bilateralIncrementRoot n +
      ((((t - bilateralIncrementRoot n).toNat - 1) + 1 : ℕ) : ℤ) = t := by omega
  have hm₁ := integral_bilateralArray_coordinate_eq_origin ρ hS
    (bilateralIncrementRoot n) (t - bilateralIncrementRoot n).toNat
  have hm₂ := integral_bilateralArray_coordinate_eq_origin ρ hS
    (bilateralIncrementRoot n) ((t - bilateralIncrementRoot n).toNat - 1)
  simp only [h₁] at hm₁
  simp only [h₂] at hm₂
  exact congrArg₂ (fun a b : ℝ => a - b) hm₁ hm₂

/-- At and left of the root the expectation is the unit-interval mean. -/
theorem integral_bilateralArrayIncrements_of_le_root
    (ρ : ProbabilityMeasure BilateralArray)
    (hS : MeasurePreserving bilateralArrayShift (ρ : Measure _) (ρ : Measure _))
    (n : ℕ) (t : ℤ) (ht : t ≤ bilateralIncrementRoot n) :
    (∫ x, bilateralArrayIncrements n x t ∂(ρ : Measure _)) = (∫ x : BilateralArray, x ⟨(0, (((0) + 1 : ℕ) : ℤ)), by omega⟩ ∂(ρ : Measure _)) := by
  by_cases he : t = bilateralIncrementRoot n
  · subst t
    simp_rw [bilateralArrayIncrements_at_root]
    exact integral_bilateralArray_coordinate_eq_origin ρ hS _ 0
  · simp_rw [bilateralArrayIncrements_of_lt_root n _ t (by omega)]
    exact integral_bilateralArray_coordinate_eq_origin ρ hS _ 0

/-- Positive coordinate expectations use only origin intervals of positive length. -/
theorem integral_bilateralArrayIncrements_nonneg_coordinate
    (ρ : ProbabilityMeasure BilateralArray)
    (hS : MeasurePreserving bilateralArrayShift (ρ : Measure _) (ρ : Measure _))
    (hi : ∀ p : BilateralInterval, Integrable (fun x : BilateralArray => x p) (ρ : Measure _))
    (n t : ℕ) :
    (∫ x, bilateralArrayIncrements n x (t : ℤ) ∂(ρ : Measure _)) =
      (∫ x : BilateralArray, x ⟨(0, ((((n + t + 1)) + 1 : ℕ) : ℤ)), by omega⟩ ∂(ρ : Measure _)) - (∫ x : BilateralArray, x ⟨(0, ((((n + t)) + 1 : ℕ) : ℤ)), by omega⟩ ∂(ρ : Measure _)) := by
  have ht : bilateralIncrementRoot n < (t : ℤ) := by
    dsimp only [bilateralIncrementRoot]
    omega
  rw [integral_bilateralArrayIncrements_of_root_lt ρ hS hi n t ht]
  have hd : ((t : ℤ) - bilateralIncrementRoot n).toNat = n + t + 1 := by
    dsimp only [bilateralIncrementRoot]
    omega
  simp only [hd, Nat.add_sub_cancel]

/-- The boundary r=h belongs to the unit-interval branch. -/
theorem integral_bilateralArrayIncrements_neg_coordinate
    (ρ : ProbabilityMeasure BilateralArray)
    (hS : MeasurePreserving bilateralArrayShift (ρ : Measure _) (ρ : Measure _))
    (hi : ∀ p : BilateralInterval, Integrable (fun x : BilateralArray => x p) (ρ : Measure _))
    (n h : ℕ) :
    (∫ x, bilateralArrayIncrements n x (-(h : ℤ)) ∂(ρ : Measure _)) =
      if n + 1 ≤ h then (∫ x : BilateralArray, x ⟨(0, (((0) + 1 : ℕ) : ℤ)), by omega⟩ ∂(ρ : Measure _)) else
        (∫ x : BilateralArray, x ⟨(0, ((((n + 1 - h)) + 1 : ℕ) : ℤ)), by omega⟩ ∂(ρ : Measure _)) - (∫ x : BilateralArray, x ⟨(0, ((((n - h)) + 1 : ℕ) : ℤ)), by omega⟩ ∂(ρ : Measure _)) := by
  split_ifs with he
  · exact integral_bilateralArrayIncrements_of_le_root ρ hS n _ (by
      dsimp only [bilateralIncrementRoot]
      omega)
  · have ht : bilateralIncrementRoot n < -(h : ℤ) := by
      dsimp only [bilateralIncrementRoot]
      omega
    rw [integral_bilateralArrayIncrements_of_root_lt ρ hS hi n _ ht]
    have hd : (-(h : ℤ) - bilateralIncrementRoot n).toNat = n + 1 - h := by
      dsimp only [bilateralIncrementRoot]
      omega
    have heindex : n + 1 - h - 1 = n - h := by omega
    simp only [hd, heindex]

private theorem sum_range_originMean_differences
    (ρ : ProbabilityMeasure BilateralArray) (M t : ℕ) :
    (∑ n ∈ Finset.range M,
      ((∫ x : BilateralArray, x ⟨(0, ((((n + t + 1)) + 1 : ℕ) : ℤ)), by omega⟩ ∂(ρ : Measure _)) - (∫ x : BilateralArray, x ⟨(0, ((((n + t)) + 1 : ℕ) : ℤ)), by omega⟩ ∂(ρ : Measure _)))) =
      (∫ x : BilateralArray, x ⟨(0, ((((M + t)) + 1 : ℕ) : ℤ)), by omega⟩ ∂(ρ : Measure _)) - (∫ x : BilateralArray, x ⟨(0, (((t) + 1 : ℕ) : ℤ)), by omega⟩ ∂(ρ : Measure _)) := by
  induction M with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, zero_add, sub_self]
  | succ M ih =>
      rw [Finset.sum_range_succ, ih]
      have he : M + 1 + t = M + t + 1 := by omega
      simp only [he]
      ring

/-- Exact finite sampler mean at a nonnegative integer coordinate. -/
theorem integral_uniform_bilateralArrayIncrements_nonneg_coordinate
    (ρ : ProbabilityMeasure BilateralArray)
    (hS : MeasurePreserving bilateralArrayShift (ρ : Measure _) (ρ : Measure _))
    (hi : ∀ p : BilateralInterval, Integrable (fun x : BilateralArray => x p) (ρ : Measure _))
    (N t : ℕ) :
    (∫ p : BilateralArray × Fin (N + 1), bilateralArrayIncrements p.2.val p.1 (t : ℤ)
      ∂uniformOriginProduct (ρ : Measure _) N) =
      ((∫ x : BilateralArray, x ⟨(0, ((((N + 1 + t)) + 1 : ℕ) : ℤ)), by omega⟩ ∂(ρ : Measure _)) - (∫ x : BilateralArray, x ⟨(0, (((t) + 1 : ℕ) : ℤ)), by omega⟩ ∂(ρ : Measure _))) / (N + 1 : ℝ) := by
  rw [integral_uniformOrigin_family (ρ : Measure _) N
    (fun u x => bilateralArrayIncrements u.val x (t : ℤ))
    (fun u => measurable_bilateralArrayIncrements_coordinate u.val (t : ℤ))
    (fun u => integrable_bilateralArrayIncrements ρ hi u.val (t : ℤ))]
  simp_rw [integral_bilateralArrayIncrements_nonneg_coordinate ρ hS hi]
  rw [Fin.sum_univ_eq_sum_range (fun n =>
    (∫ x : BilateralArray, x ⟨(0, ((((n + t + 1)) + 1 : ℕ) : ℤ)), by omega⟩ ∂(ρ : Measure _)) - (∫ x : BilateralArray, x ⟨(0, ((((n + t)) + 1 : ℕ) : ℤ)), by omega⟩ ∂(ρ : Measure _))),
    sum_range_originMean_differences]

private theorem sum_range_negative_originMean_add
    (ρ : ProbabilityMeasure BilateralArray) (h : ℕ) (hh : 0 < h) (k : ℕ) :
    (∑ n ∈ Finset.range (h + k),
      (if n + 1 ≤ h then (∫ x : BilateralArray, x ⟨(0, (((0) + 1 : ℕ) : ℤ)), by omega⟩ ∂(ρ : Measure _)) else
        (∫ x : BilateralArray, x ⟨(0, ((((n + 1 - h)) + 1 : ℕ) : ℤ)), by omega⟩ ∂(ρ : Measure _)) - (∫ x : BilateralArray, x ⟨(0, ((((n - h)) + 1 : ℕ) : ℤ)), by omega⟩ ∂(ρ : Measure _)))) =
      (∫ x : BilateralArray, x ⟨(0, (((k) + 1 : ℕ) : ℤ)), by omega⟩ ∂(ρ : Measure _)) + ((h - 1 : ℕ) : ℝ) * (∫ x : BilateralArray, x ⟨(0, (((0) + 1 : ℕ) : ℤ)), by omega⟩ ∂(ρ : Measure _)) := by
  induction k with
  | zero =>
      have hs : (∑ n ∈ Finset.range h,
          (if n + 1 ≤ h then (∫ x : BilateralArray, x ⟨(0, (((0) + 1 : ℕ) : ℤ)), by omega⟩ ∂(ρ : Measure _)) else
            (∫ x : BilateralArray, x ⟨(0, ((((n + 1 - h)) + 1 : ℕ) : ℤ)), by omega⟩ ∂(ρ : Measure _)) - (∫ x : BilateralArray, x ⟨(0, ((((n - h)) + 1 : ℕ) : ℤ)), by omega⟩ ∂(ρ : Measure _)))) =
          ∑ _n ∈ Finset.range h, (∫ x : BilateralArray, x ⟨(0, (((0) + 1 : ℕ) : ℤ)), by omega⟩ ∂(ρ : Measure _)) := by
        apply Finset.sum_congr rfl
        intro n hn
        have hn' := Finset.mem_range.mp hn
        rw [ite_eq_left (by omega)]
      rw [Nat.add_zero, hs]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hc : (h : ℝ) = ((h - 1 : ℕ) : ℝ) + 1 := by
        exact_mod_cast (show h = h - 1 + 1 by omega)
      rw [hc]
      ring
  | succ k ih =>
      rw [show h + (k + 1) = (h + k) + 1 by omega, Finset.sum_range_succ, ih]
      rw [ite_eq_right (by omega)]
      have h₁ : h + k + 1 - h = k + 1 := by omega
      have h₂ : h + k - h = k := by omega
      simp only [h₁, h₂]
      ring

/-- Exact finite sampler mean at a negative coordinate, including M=h. -/
theorem integral_uniform_bilateralArrayIncrements_neg_coordinate
    (ρ : ProbabilityMeasure BilateralArray)
    (hS : MeasurePreserving bilateralArrayShift (ρ : Measure _) (ρ : Measure _))
    (hi : ∀ p : BilateralInterval, Integrable (fun x : BilateralArray => x p) (ρ : Measure _))
    (N h : ℕ) (hh : 0 < h) (hN : h ≤ N + 1) :
    (∫ p : BilateralArray × Fin (N + 1), bilateralArrayIncrements p.2.val p.1 (-(h : ℤ))
      ∂uniformOriginProduct (ρ : Measure _) N) =
      ((∫ x : BilateralArray, x ⟨(0, ((((N + 1 - h)) + 1 : ℕ) : ℤ)), by omega⟩ ∂(ρ : Measure _)) +
        ((h - 1 : ℕ) : ℝ) * (∫ x : BilateralArray, x ⟨(0, (((0) + 1 : ℕ) : ℤ)), by omega⟩ ∂(ρ : Measure _))) / (N + 1 : ℝ) := by
  rw [integral_uniformOrigin_family (ρ : Measure _) N
    (fun u x => bilateralArrayIncrements u.val x (-(h : ℤ)))
    (fun u => measurable_bilateralArrayIncrements_coordinate u.val (-(h : ℤ)))
    (fun u => integrable_bilateralArrayIncrements ρ hi u.val (-(h : ℤ)))]
  simp_rw [integral_bilateralArrayIncrements_neg_coordinate ρ hS hi]
  rw [Fin.sum_univ_eq_sum_range (fun n =>
    if n + 1 ≤ h then (∫ x : BilateralArray, x ⟨(0, (((0) + 1 : ℕ) : ℤ)), by omega⟩ ∂(ρ : Measure _)) else
      (∫ x : BilateralArray, x ⟨(0, ((((n + 1 - h)) + 1 : ℕ) : ℤ)), by omega⟩ ∂(ρ : Measure _)) - (∫ x : BilateralArray, x ⟨(0, ((((n - h)) + 1 : ℕ) : ℤ)), by omega⟩ ∂(ρ : Measure _)))]
  have hs := sum_range_negative_originMean_add ρ h hh (N + 1 - h)
  rw [Nat.add_sub_of_le hN] at hs
  rw [hs]

/-- Conditional on the actual normalized origin expectations, every actual
sampled increment coordinate has limiting mean q. -/
theorem tendsto_integral_uniform_bilateralArrayIncrements
    (ρ : ProbabilityMeasure BilateralArray)
    (hS : MeasurePreserving bilateralArrayShift (ρ : Measure _) (ρ : Measure _))
    (hi : ∀ p : BilateralInterval, Integrable (fun x : BilateralArray => x p) (ρ : Measure _))
    (q : ℝ)
    (ha : Tendsto (fun n : ℕ => (∫ x : BilateralArray, x ⟨(0, (((n) + 1 : ℕ) : ℤ)), by omega⟩ ∂(ρ : Measure _)) / (n + 1 : ℝ)) atTop (𝓝 q))
    (t : ℤ) :
    Tendsto (fun N : ℕ =>
      ∫ p : BilateralArray × Fin (N + 1), bilateralArrayIncrements p.2.val p.1 t
        ∂uniformOriginProduct (ρ : Measure _) N) atTop (𝓝 q) := by
  -- a(0) is never consumed; every array coordinate in a(n), n>=1, has length n.
  let f : ℕ → ℝ := fun n => ∫ x : BilateralArray,
    x ⟨(0, ((n + 1 : ℕ) : ℤ)), by omega⟩ ∂(ρ : Measure _)
  change Tendsto (fun n : ℕ => f n / (n + 1 : ℝ)) atTop (𝓝 q) at ha
  let a : ℕ → ℝ := fun n => f (n - 1)
  have ha' : Tendsto (fun n : ℕ => a (n + 1) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 q) := by
    simpa only [a, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] using ha
  by_cases ht : 0 ≤ t
  · let k := t.toNat
    have hk : (k : ℤ) = t := by dsimp only [k]; omega
    rw [← hk]
    have hlim := (tendsto_add_atTop_iff_nat 1).2
      (tendsto_positive_coordinate_increment_mean a q ha' k)
    apply hlim.congr'
    filter_upwards [] with N
    rw [sum_positive_coordinate_increments,
      integral_uniform_bilateralArrayIncrements_nonneg_coordinate ρ hS hi]
    change (a (N + 1 + k + 1) - a (k + 1)) / ((N + 1 : ℕ) : ℝ) =
      (f (N + 1 + k) - f k) / (N + 1 : ℝ)
    simp only [a, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  · let h := (-t).toNat
    have hh : 0 < h := by dsimp only [h]; omega
    have he : -(h : ℤ) = t := by dsimp only [h]; omega
    rw [← he]
    have hlim := (tendsto_add_atTop_iff_nat 1).2
      (tendsto_negative_coordinate_increment_mean a q ha' h hh)
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop h] with N hN
    rw [sum_negative_coordinate_increments a h (N + 1) hh (by omega),
      integral_uniform_bilateralArrayIncrements_neg_coordinate ρ hS hi N h hh (by omega)]
    change (a (N + 1 - h + 1) + ((h - 1 : ℕ) : ℝ) * a 1) / ((N + 1 : ℕ) : ℝ) =
      (f (N + 1 - h) + ((h - 1 : ℕ) : ℝ) * f 0) / (N + 1 : ℝ)
    simp only [a, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]

/-- Actual nonnegative superadditive source arrays yield nonnegative sampled increments. -/
theorem ae_nonneg_uniform_bilateralArrayIncrements
    (ρ : ProbabilityMeasure BilateralArray)
    (hnonneg : ∀ᵐ x ∂(ρ : Measure BilateralArray), ∀ p, 0 ≤ x p)
    (hadd : ∀ᵐ x ∂(ρ : Measure BilateralArray), ∀ (a b c : ℤ) (hab : a < b) (hbc : b < c),
      x ⟨(a, b), hab⟩ + x ⟨(b, c), hbc⟩ ≤ x ⟨(a, c), by omega⟩)
    (N : ℕ) (t : ℤ) :
    ∀ᵐ p ∂uniformOriginProduct (ρ : Measure _) N,
      0 ≤ bilateralArrayIncrements p.2.val p.1 t := by
  have hn := (uniformOriginProduct_fst (ρ : Measure BilateralArray) N).quasiMeasurePreserving.ae hnonneg
  have hs := (uniformOriginProduct_fst (ρ : Measure BilateralArray) N).quasiMeasurePreserving.ae hadd
  filter_upwards [hn, hs] with p hp hs
  exact bilateralArrayIncrements_nonneg_of_nonneg_superadditive p.1 hp hs p.2.val t

/-- Convergence and actual nonnegativity give a uniform absolute first-moment
bound at each coordinate. No uniform integrability or second moment is assumed. -/
theorem exists_uniform_abs_integral_bilateralArrayIncrements_le
    (ρ : ProbabilityMeasure BilateralArray)
    (hS : MeasurePreserving bilateralArrayShift (ρ : Measure _) (ρ : Measure _))
    (hi : ∀ p : BilateralInterval, Integrable (fun x : BilateralArray => x p) (ρ : Measure _))
    (hnonneg : ∀ᵐ x ∂(ρ : Measure BilateralArray), ∀ p, 0 ≤ x p)
    (hadd : ∀ᵐ x ∂(ρ : Measure BilateralArray), ∀ (a b c : ℤ) (hab : a < b) (hbc : b < c),
      x ⟨(a, b), hab⟩ + x ⟨(b, c), hbc⟩ ≤ x ⟨(a, c), by omega⟩)
    (q : ℝ)
    (ha : Tendsto (fun n : ℕ => (∫ x : BilateralArray, x ⟨(0, (((n) + 1 : ℕ) : ℤ)), by omega⟩ ∂(ρ : Measure _)) / (n + 1 : ℝ)) atTop (𝓝 q))
    (t : ℤ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      (∫ p : BilateralArray × Fin (N + 1), |bilateralArrayIncrements p.2.val p.1 t|
        ∂uniformOriginProduct (ρ : Measure _) N) ≤ C := by
  obtain ⟨C, hC⟩ := (tendsto_integral_uniform_bilateralArrayIncrements ρ hS hi q ha t).bddAbove_range
  refine ⟨max 0 C, le_max_left _ _, fun N => ?_⟩
  have he : (∫ p : BilateralArray × Fin (N + 1), |bilateralArrayIncrements p.2.val p.1 t|
      ∂uniformOriginProduct (ρ : Measure _) N) =
      ∫ p : BilateralArray × Fin (N + 1), bilateralArrayIncrements p.2.val p.1 t
        ∂uniformOriginProduct (ρ : Measure _) N := by
    apply integral_congr_ae
    filter_upwards [ae_nonneg_uniform_bilateralArrayIncrements ρ hnonneg hadd N t] with p hp
    exact abs_of_nonneg hp
  rw [he]
  exact (hC (Set.mem_range_self N)).trans (le_max_right _ _)

end LPPDifferentiability
