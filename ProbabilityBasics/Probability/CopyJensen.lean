/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import ProbabilityBasics.Probability.CenteredRpowSum
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Independent-copy Jensen

The first step of the finite-moment symmetrization construction.
Genuine coordinate moments produce all needed sum and copy-difference
integrability. Jensen is applied on the second copy, followed by Fubini.
Independence among the coordinates is not required.
-/

public section

open MeasureTheory

namespace LPPDifferentiability

private theorem integrable_abs_sub_rpow_of_moments
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g)
    {r : ℝ} (hr : 1 ≤ r)
    (hfr : Integrable (fun x => |f x| ^ r) P)
    (hgr : Integrable (fun x => |g x| ^ r) P) :
    Integrable (fun x => |f x - g x| ^ r) P := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hp0 : ENNReal.ofReal r ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hr0)
  have hfm : MemLp f (ENNReal.ofReal r) P := by
    apply (integrable_norm_rpow_iff hf.aestronglyMeasurable hp0
      ENNReal.ofReal_ne_top).mp
    simpa only [ENNReal.toReal_ofReal hr0.le, Real.norm_eq_abs] using hfr
  have hgm : MemLp g (ENNReal.ofReal r) P := by
    apply (integrable_norm_rpow_iff hg.aestronglyMeasurable hp0
      ENNReal.ofReal_ne_top).mp
    simpa only [ENNReal.toReal_ofReal hr0.le, Real.norm_eq_abs] using hgr
  simpa only [ENNReal.toReal_ofReal hr0.le, Real.norm_eq_abs, Pi.sub_apply] using
    (hfm.sub hgm).integrable_norm_rpow hp0 ENNReal.ofReal_ne_top

private theorem convexOn_abs_rpow {r : ℝ} (hr : 1 ≤ r) :
    ConvexOn ℝ Set.univ (fun t : ℝ => |t| ^ r) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hnorm : |a * x + b * y| ≤ a * |x| + b * |y| := by
    calc
      |a * x + b * y| ≤ |a * x| + |b * y| := abs_add_le _ _
      _ = a * |x| + b * |y| := by
        rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  change |a * x + b * y| ^ r ≤ a * |x| ^ r + b * |y| ^ r
  exact (Real.rpow_le_rpow (abs_nonneg _) hnorm (zero_le_one.trans hr)).trans
    ((convexOn_rpow hr).2 (abs_nonneg x) (abs_nonneg y) ha hb hab)

private theorem integral_abs_rpow_le_copy_difference
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : Ω → ℝ) (r : ℝ) (hr : 1 ≤ r)
    (hS : Integrable S P) (hmean : ∫ x, S x ∂P = 0)
    (hSr : Integrable (fun x => |S x| ^ r) P)
    (hprod : Integrable (fun p : Ω × Ω => |S p.1 - S p.2| ^ r) (P.prod P)) :
    (∫ x, |S x| ^ r ∂P) ≤ ∫ p, |S p.1 - S p.2| ^ r ∂P.prod P := by
  have hJ : ∀ᵐ x ∂P, |S x| ^ r ≤ ∫ y, |S x - S y| ^ r ∂P := by
    filter_upwards [hprod.prod_right_ae] with x hx
    have hdiff : Integrable (fun y => S x - S y) P := (integrable_const _).sub hS
    have hmeanDiff : (∫ y, S x - S y ∂P) = S x := by
      rw [integral_sub (integrable_const _) hS, integral_const, hmean]
      simp only [probReal_univ, one_smul, sub_zero]
    have hj := (convexOn_abs_rpow hr).map_integral_le
      (continuous_abs.rpow_const (fun _ => Or.inr (zero_le_one.trans hr))).continuousOn
      isClosed_univ (Filter.Eventually.of_forall (fun _ => Set.mem_univ _)) hdiff hx
    rw [hmeanDiff] at hj
    exact hj
  calc
    (∫ x, |S x| ^ r ∂P) ≤ ∫ x, ∫ y, |S x - S y| ^ r ∂P ∂P :=
      integral_mono_ae hSr hprod.integral_prod_left hJ
    _ = ∫ p, |S p.1 - S p.2| ^ r ∂P.prod P := (integral_prod _ hprod).symm

/-- Jensen on an independent copy bounds the rth moment of a finite centered
sum by the rth moment of its copy differences. The coordinates themselves
need not be independent. All sum and product integrability is derived from
the actual finite coordinate moments. -/
theorem integral_abs_rpow_sum_le_integral_copy_difference
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (s : Finset ι) (Z : ι → Ω → ℝ)
    (hZ : ∀ i ∈ s, Measurable (Z i)) {r : ℝ} (hr : 1 ≤ r)
    (hMoment : ∀ i ∈ s, Integrable (fun x => |Z i x| ^ r) P)
    (hmean : ∀ i ∈ s, (∫ x, Z i x ∂P) = 0) :
    (∫ x, |∑ i ∈ s, Z i x| ^ r ∂P) ≤
      ∫ p, |∑ i ∈ s, (Z i p.1 - Z i p.2)| ^ r ∂P.prod P := by
  have hFirst (i : ι) (hi : i ∈ s) : Integrable (Z i) P :=
    integrable_of_integrable_abs_rpow P (hZ i hi) hr (hMoment i hi)
  have hSum := integrable_sum_and_abs_rpow_of_moments P s Z hZ hr hMoment
  have hCopyMeas (i : ι) (hi : i ∈ s) :
      Measurable (fun p : Ω × Ω => Z i p.1 - Z i p.2) :=
    ((hZ i hi).comp measurable_fst).sub ((hZ i hi).comp measurable_snd)
  have hCopyMoment (i : ι) (hi : i ∈ s) :
      Integrable (fun p : Ω × Ω => |Z i p.1 - Z i p.2| ^ r) (P.prod P) :=
    integrable_abs_sub_rpow_of_moments (P.prod P)
      ((hZ i hi).comp measurable_fst) ((hZ i hi).comp measurable_snd) hr
      ((hMoment i hi).comp_fst P) ((hMoment i hi).comp_snd P)
  have hCopySum := integrable_sum_and_abs_rpow_of_moments (P.prod P) s
    (fun i (p : Ω × Ω) => Z i p.1 - Z i p.2) hCopyMeas hr hCopyMoment
  have hSumMean : (∫ x, ∑ i ∈ s, Z i x ∂P) = 0 := by
    rw [integral_finsetSum s hFirst]
    exact Finset.sum_eq_zero hmean
  have hprod : Integrable
      (fun p : Ω × Ω => |(∑ i ∈ s, Z i p.1) - ∑ i ∈ s, Z i p.2| ^ r)
      (P.prod P) := by
    simpa only [Finset.sum_sub_distrib] using hCopySum.2
  simpa only [Finset.sum_sub_distrib] using
    integral_abs_rpow_le_copy_difference P (fun x => ∑ i ∈ s, Z i x) r hr
      hSum.1 hSumMean hSum.2 hprod

end LPPDifferentiability
