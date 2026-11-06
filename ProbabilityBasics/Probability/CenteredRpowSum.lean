/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.Independence.Integration
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Fair-sign moment bounds

This module supplies the fair-sign step, with deterministic coefficients, for the
independent centered-sum bound. The copy and symmetrization steps for general
centered random variables are not in this module.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace LPPDifferentiability

/-- A finite rth absolute moment gives a genuine first moment. -/
theorem integrable_of_integrable_abs_rpow {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {Z : Ω → ℝ} (hZ : Measurable Z)
    {r : ℝ} (hr : 1 ≤ r) (hMoment : Integrable (fun ω => |Z ω| ^ r) μ) :
    Integrable Z μ := by
  have hnorm : Integrable (fun ω => ‖Z ω‖ ^ r) μ := by
    simpa only [Real.norm_eq_abs] using hMoment
  have hfirst := integrable_norm_rpow_of_le hZ.aestronglyMeasurable
    (p := 1) (q := r) (by norm_num) (by linarith only [hr]) hr hnorm
  exact (integrable_norm_iff hZ.aestronglyMeasurable).mp
    (by simpa only [Real.rpow_one] using hfirst)

/-- Actual coordinate rth moments give both the finite sum's first moment and
its rth absolute moment. No independence or asserted sum bound is needed. -/
theorem integrable_sum_and_abs_rpow_of_moments {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (s : Finset ι) (Z : ι → Ω → ℝ)
    (hZ : ∀ i ∈ s, Measurable (Z i)) {r : ℝ} (hr : 1 ≤ r)
    (hMoment : ∀ i ∈ s, Integrable (fun ω => |Z i ω| ^ r) μ) :
    Integrable (fun ω => ∑ i ∈ s, Z i ω) μ ∧
      Integrable (fun ω => |∑ i ∈ s, Z i ω| ^ r) μ := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hp0 : ENNReal.ofReal r ≠ 0 := by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hr0
  have hmem (i : ι) (hi : i ∈ s) : MemLp (Z i) (ENNReal.ofReal r) μ := by
    apply (integrable_norm_rpow_iff (hZ i hi).aestronglyMeasurable hp0
      ENNReal.ofReal_ne_top).mp
    simpa only [ENNReal.toReal_ofReal hr0.le, Real.norm_eq_abs] using hMoment i hi
  have hsum := memLp_finsetSum s hmem
  refine ⟨integrable_finsetSum s (fun i hi =>
    integrable_of_integrable_abs_rpow μ (hZ i hi) hr (hMoment i hi)), ?_⟩
  simpa only [ENNReal.toReal_ofReal hr0.le, Real.norm_eq_abs] using
    hsum.integrable_norm_rpow hp0 ENNReal.ofReal_ne_top

private theorem sum_sq_rpow_le_sum_abs_rpow {ι : Type*} (s : Finset ι)
    (a : ι → ℝ) {r : ℝ} (hr0 : 0 < r) (hr2 : r ≤ 2) :
    (∑ i ∈ s, a i ^ 2) ^ (r / 2) ≤ ∑ i ∈ s, |a i| ^ r := by
  classical
  have hp0 : 0 ≤ r / 2 := by positivity
  have hp1 : r / 2 ≤ 1 := by linarith only [hr2]
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Real.zero_rpow (by positivity : r / 2 ≠ 0), le_refl]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    calc
      (a i ^ 2 + ∑ j ∈ s, a j ^ 2) ^ (r / 2) ≤
          (a i ^ 2) ^ (r / 2) + (∑ j ∈ s, a j ^ 2) ^ (r / 2) :=
        Real.rpow_add_le_add_rpow (sq_nonneg _) (Finset.sum_nonneg fun j _ => sq_nonneg _)
          hp0 hp1
      _ ≤ |a i| ^ r + ∑ j ∈ s, |a j| ^ r := by
        have heq : (a i ^ 2) ^ (r / 2) = |a i| ^ r := by
          rw [← sq_abs, ← Real.rpow_natCast _ 2, ← Real.rpow_mul (abs_nonneg _)]
          congr 1
          ring
        rw [heq]
        exact add_le_add le_rfl ih

/-- Each coordinate of the literal product of fair Boolean laws is centered. -/
theorem integral_fair_sign {ι : Type*} [Fintype ι] (i : ι) :
    (∫ ε : ι → Bool, (if ε i then (1 : ℝ) else -1)
      ∂Measure.pi (fun _ : ι => (PMF.uniformOfFintype Bool).toMeasure)) = 0 := by
  rw [integral_comp_eval (μ := fun _ : ι => (PMF.uniformOfFintype Bool).toMeasure)
    (i := i) (f := fun b : Bool => if b then (1 : ℝ) else -1)
    (by exact .of_discrete)]
  simp [PMF.integral_eq_sum, PMF.uniformOfFintype_apply]

/-- The signed deterministic sum has exactly its Euclidean second moment. -/
theorem integral_sq_sum_fair_sign {ι : Type*} [Fintype ι]
    (s : Finset ι) (a : ι → ℝ) :
    (∫ ε : ι → Bool, (∑ i ∈ s, (if ε i then (1 : ℝ) else -1) * a i) ^ 2
      ∂Measure.pi (fun _ : ι => (PMF.uniformOfFintype Bool).toMeasure)) =
      ∑ i ∈ s, a i ^ 2 := by
  classical
  let μ : Measure (ι → Bool) :=
    Measure.pi (fun _ : ι => (PMF.uniformOfFintype Bool).toMeasure)
  let X : ι → (ι → Bool) → ℝ := fun i ε => (if ε i then (1 : ℝ) else -1) * a i
  have hIndep : iIndepFun X μ :=
    iIndepFun_pi (fun i => (measurable_of_countable (fun b : Bool =>
      (if b then (1 : ℝ) else -1) * a i)).aemeasurable)
  have hmean (i : ι) : (∫ ε, X i ε ∂μ) = 0 := by
    dsimp only [X]
    rw [integral_mul_const, integral_fair_sign, zero_mul]
  have hpair (i j : ι) : (∫ ε, X i ε * X j ε ∂μ) = if i = j then a i ^ 2 else 0 := by
    by_cases hij : i = j
    · subst j
      have heq : (fun ε => X i ε * X i ε) = fun _ => a i ^ 2 := by
        funext ε
        dsimp only [X]
        split_ifs <;> ring
      rw [heq]
      simp only [integral_const, probReal_univ, one_smul, ite_true]
    · simp only [hij, ite_false]
      rw [(hIndep.indepFun hij).integral_fun_mul_eq_mul_integral
        (.of_discrete) (.of_discrete), hmean, hmean, zero_mul]
  change (∫ ε, (∑ i ∈ s, X i ε) ^ 2 ∂μ) = _
  simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => Integrable.of_finite)]
  simp_rw [integral_finsetSum _ (fun j _ => Integrable.of_finite), hpair, Finset.sum_ite_eq]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [hi, ite_true, pow_two]

/-- For actual independent fair signs and fixed real coefficients, the rth moment
is bounded by the sum of coefficient moments. Integrability is produced. -/
theorem integrable_and_integral_abs_rpow_sum_fair_sign_le {ι : Type*} [Fintype ι]
    (s : Finset ι) (a : ι → ℝ) {r : ℝ} (hr0 : 0 < r) (hr2 : r ≤ 2) :
    Integrable (fun ε : ι → Bool => |∑ i ∈ s, (if ε i then (1 : ℝ) else -1) * a i| ^ r)
      (Measure.pi (fun _ : ι => (PMF.uniformOfFintype Bool).toMeasure)) ∧
    (∫ ε : ι → Bool, |∑ i ∈ s, (if ε i then (1 : ℝ) else -1) * a i| ^ r
      ∂Measure.pi (fun _ : ι => (PMF.uniformOfFintype Bool).toMeasure)) ≤
      ∑ i ∈ s, |a i| ^ r := by
  classical
  let μ : Measure (ι → Bool) :=
    Measure.pi (fun _ : ι => (PMF.uniformOfFintype Bool).toMeasure)
  let S : (ι → Bool) → ℝ := fun ε => ∑ i ∈ s, (if ε i then (1 : ℝ) else -1) * a i
  refine ⟨Integrable.of_finite, ?_⟩
  have hp0 : 0 ≤ r / 2 := by positivity
  have hp1 : r / 2 ≤ 1 := by linarith only [hr2]
  have hj := (Real.concaveOn_rpow hp0 hp1).le_map_integral
    (Real.continuous_rpow_const hp0).continuousOn isClosed_Ici
    (μ := μ) (f := fun ε => S ε ^ 2)
    (Filter.Eventually.of_forall (fun ε => sq_nonneg (S ε)))
    Integrable.of_finite Integrable.of_finite
  have heq (x : ℝ) : (x ^ 2) ^ (r / 2) = |x| ^ r := by
    rw [← sq_abs, ← Real.rpow_natCast _ 2, ← Real.rpow_mul (abs_nonneg _)]
    congr 1
    ring
  simp_rw [heq] at hj
  have hs : (∫ ε, S ε ^ 2 ∂μ) = ∑ i ∈ s, a i ^ 2 := integral_sq_sum_fair_sign s a
  rw [hs] at hj
  exact hj.trans (sum_sq_rpow_le_sum_abs_rpow s a hr0 hr2)

end LPPDifferentiability
