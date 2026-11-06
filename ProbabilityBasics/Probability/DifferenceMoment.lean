/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Algebra.Order.Ring.Abs

/-!
# Moments of differences under product probability measures

The pointwise power bound and the actual coordinate moments produce an
integrable difference moment under the product law. For two probability
marginals the bound uses their separate moments; for two independent copies
from one law this gives the factor `2^r`.
-/

@[expose] public section

open MeasureTheory

namespace LPPDifferentiability

/-- The `r`th power of a difference is bounded by the two `r`th powers when
`r` is at least one. -/
theorem abs_sub_rpow_le_two_mul_add_abs_rpow {x y r : ℝ} (hr : 1 ≤ r) :
    |x - y| ^ r ≤ (2 : ℝ) ^ (r - 1) * (|x| ^ r + |y| ^ r) := by
  have hmean : ((|x| + |y|) / 2) ^ r ≤ (|x| ^ r + |y| ^ r) / 2 := by
    have hconvex := (convexOn_rpow hr).2
      (Set.mem_Ici.mpr (abs_nonneg x)) (Set.mem_Ici.mpr (abs_nonneg y))
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1)
    have hbase :
        (1 / 2 : ℝ) * |x| + (1 / 2 : ℝ) * |y| = (|x| + |y|) / 2 := by
      ring
    have hvalues :
        (1 / 2 : ℝ) * |x| ^ r + (1 / 2 : ℝ) * |y| ^ r =
          (|x| ^ r + |y| ^ r) / 2 := by
      ring
    simpa only [smul_eq_mul, hbase, hvalues] using hconvex
  have htriangle : |x - y| ≤ |x| + |y| := by
    calc
      |x - y| = |x + -y| := by rw [sub_eq_add_neg]
      _ ≤ |x| + |-y| := abs_add_le _ _
      _ = |x| + |y| := by simp only [abs_neg]
  have htwice : (2 : ℝ) * ((|x| + |y|) / 2) = |x| + |y| := by
    ring
  calc
    |x - y| ^ r ≤ (|x| + |y|) ^ r :=
      Real.rpow_le_rpow (abs_nonneg _) htriangle (le_trans (by norm_num) hr)
    _ = ((2 : ℝ) * ((|x| + |y|) / 2)) ^ r := by rw [htwice]
    _ = 2 ^ r * ((|x| + |y|) / 2) ^ r :=
      Real.mul_rpow (by norm_num)
        (div_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (by norm_num))
    _ ≤ 2 ^ r * ((|x| ^ r + |y| ^ r) / 2) :=
      mul_le_mul_of_nonneg_left hmean (Real.rpow_nonneg (by norm_num) r)
    _ = 2 ^ (r - 1) * (|x| ^ r + |y| ^ r) := by
      rw [Real.rpow_sub_one (by norm_num : (2 : ℝ) ≠ 0)]
      ring

/-- If the two measurable real variables have integrable `r`th absolute
moments under probability measures, their difference moment is integrable
under the actual product measure. -/
theorem integrable_abs_sub_rpow_prod
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (ν : Measure β) [IsProbabilityMeasure ν]
    {X : α → ℝ} {Y : β → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (r : ℝ) (hr : 1 ≤ r)
    (hXr : Integrable (fun x => |X x| ^ r) μ)
    (hYr : Integrable (fun y => |Y y| ^ r) ν) :
    Integrable (fun p : α × β => |X p.1 - Y p.2| ^ r) (μ.prod ν) := by
  let momentX : α × β → ℝ := fun p => |X p.1| ^ r
  let momentY : α × β → ℝ := fun p => |Y p.2| ^ r
  let bound : α × β → ℝ := fun p => (2 : ℝ) ^ (r - 1) * (momentX p + momentY p)
  have hmomentX : Integrable momentX (μ.prod ν) := by
    exact hXr.comp_fst ν
  have hmomentY : Integrable momentY (μ.prod ν) := by
    exact hYr.comp_snd μ
  have hbound : Integrable bound (μ.prod ν) := by
    exact (hmomentX.add hmomentY).const_mul ((2 : ℝ) ^ (r - 1))
  have hdiff_meas : Measurable (fun p : α × β => |X p.1 - Y p.2| ^ r) := by
    exact (Real.continuous_rpow_const (le_trans (by norm_num) hr)).measurable.comp
      (continuous_abs.measurable.comp ((hX.comp measurable_fst).sub (hY.comp measurable_snd)))
  apply hbound.mono' hdiff_meas.aestronglyMeasurable
  filter_upwards [] with p
  have hp := abs_sub_rpow_le_two_mul_add_abs_rpow (x := X p.1) (y := Y p.2) hr
  simpa only [bound, momentX, momentY, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) r)] using hp

/-- The difference moment is bounded by the actual moments of the two product
coordinates. The marginals may be different probability measures. -/
theorem integral_abs_sub_rpow_prod_le
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (ν : Measure β) [IsProbabilityMeasure ν]
    {X : α → ℝ} {Y : β → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (r : ℝ) (hr : 1 ≤ r)
    (hXr : Integrable (fun x => |X x| ^ r) μ)
    (hYr : Integrable (fun y => |Y y| ^ r) ν) :
    (∫ p : α × β, |X p.1 - Y p.2| ^ r ∂μ.prod ν) ≤
      (2 : ℝ) ^ (r - 1) *
        ((∫ x, |X x| ^ r ∂μ) + (∫ y, |Y y| ^ r ∂ν)) := by
  let momentX : α × β → ℝ := fun p => |X p.1| ^ r
  let momentY : α × β → ℝ := fun p => |Y p.2| ^ r
  let bound : α × β → ℝ := fun p => (2 : ℝ) ^ (r - 1) * (momentX p + momentY p)
  have hmomentX : Integrable momentX (μ.prod ν) := hXr.comp_fst ν
  have hmomentY : Integrable momentY (μ.prod ν) := hYr.comp_snd μ
  have hdiff : Integrable (fun p : α × β => |X p.1 - Y p.2| ^ r) (μ.prod ν) :=
    integrable_abs_sub_rpow_prod μ ν hX hY r hr hXr hYr
  have hmajorant : Integrable bound (μ.prod ν) :=
    (hmomentX.add hmomentY).const_mul ((2 : ℝ) ^ (r - 1))
  have hpoint : ∀ p : α × β,
      |X p.1 - Y p.2| ^ r ≤ bound p := by
    intro p
    simpa only [bound, momentX, momentY] using
      abs_sub_rpow_le_two_mul_add_abs_rpow (x := X p.1) (y := Y p.2) hr
  have hmomentX_integral :
      (∫ p : α × β, momentX p ∂μ.prod ν) = (∫ x, |X x| ^ r ∂μ) := by
    change (∫ p, (fun x => |X x| ^ r) p.1 ∂μ.prod ν) = _
    simpa only [probReal_univ, one_smul] using
      (integral_fun_fst (μ := μ) (ν := ν) (fun x : α => |X x| ^ r))
  have hmomentY_integral :
      (∫ p : α × β, momentY p ∂μ.prod ν) = (∫ y, |Y y| ^ r ∂ν) := by
    change (∫ p, (fun y => |Y y| ^ r) p.2 ∂μ.prod ν) = _
    simpa only [probReal_univ, one_smul] using
      (integral_fun_snd (μ := μ) (ν := ν) (fun y : β => |Y y| ^ r))
  calc
    (∫ p : α × β, |X p.1 - Y p.2| ^ r ∂μ.prod ν) ≤ ∫ p, bound p ∂μ.prod ν :=
      integral_mono hdiff hmajorant hpoint
    _ = (2 : ℝ) ^ (r - 1) *
        ((∫ x, |X x| ^ r ∂μ) + (∫ y, |Y y| ^ r ∂ν)) := by
      calc
        (∫ p, bound p ∂μ.prod ν) =
            (2 : ℝ) ^ (r - 1) * (∫ p, momentX p + momentY p ∂μ.prod ν) := by
          rw [integral_const_mul]
        _ = (2 : ℝ) ^ (r - 1) *
            ((∫ p, momentX p ∂μ.prod ν) + (∫ p, momentY p ∂μ.prod ν)) := by
          rw [integral_add hmomentX hmomentY]
        _ = (2 : ℝ) ^ (r - 1) *
            ((∫ x, |X x| ^ r ∂μ) + (∫ y, |Y y| ^ r ∂ν)) := by
          rw [hmomentX_integral, hmomentY_integral]

/-- Two independent copies from one probability law have a difference moment
at most `2^r` times the actual one-coordinate moment. -/
theorem integral_self_difference_rpow_prod_le
    (P : Measure ℝ) [IsProbabilityMeasure P]
    {Z : ℝ → ℝ} (hZ : Measurable Z) (r : ℝ) (hr : 1 ≤ r)
    (hZr : Integrable (fun x => |Z x| ^ r) P) :
    (∫ p : ℝ × ℝ, |Z p.1 - Z p.2| ^ r ∂P.prod P) ≤
      (2 : ℝ) ^ r * (∫ x, |Z x| ^ r ∂P) := by
  have hpair := integral_abs_sub_rpow_prod_le P P hZ hZ r hr hZr hZr
  calc
    (∫ p : ℝ × ℝ, |Z p.1 - Z p.2| ^ r ∂P.prod P) ≤
        (2 : ℝ) ^ (r - 1) * ((∫ x, |Z x| ^ r ∂P) + (∫ x, |Z x| ^ r ∂P)) := hpair
    _ = (2 : ℝ) ^ r * (∫ x, |Z x| ^ r ∂P) := by
      rw [Real.rpow_sub_one (by norm_num : (2 : ℝ) ≠ 0)]
      ring

/-- The product difference has a genuine integrable `r`th moment whenever
the one-coordinate moment is integrable. -/
theorem integrable_self_difference_rpow_prod
    (P : Measure ℝ) [IsProbabilityMeasure P]
    {Z : ℝ → ℝ} (hZ : Measurable Z) (r : ℝ) (hr : 1 ≤ r)
    (hZr : Integrable (fun x => |Z x| ^ r) P) :
    Integrable (fun p : ℝ × ℝ => |Z p.1 - Z p.2| ^ r) (P.prod P) :=
  integrable_abs_sub_rpow_prod P P hZ hZ r hr hZr hZr

end LPPDifferentiability
