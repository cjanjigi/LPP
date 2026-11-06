/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import ProbabilityBasics.Probability.CenteredRpowSum

/-!
# Random-coefficient fair-sign moments

This file integrates the deterministic fair-sign moment bound over an arbitrary probability
space of measurable coefficients. The integrability of the product is proved from the moments
of the coordinates.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace LPPDifferentiability

/-- If each coordinate has a finite `r`-th moment, then the random fair-sign sum has a finite
`r`-th moment under the product measure. This moment is bounded by the sum of the coordinate
moments. -/
theorem integrable_and_integral_abs_rpow_sum_fair_sign_random_le
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (s : Finset ι) (Z : ι → Ω → ℝ)
    (hZ : ∀ i ∈ s, Measurable (Z i))
    {r : ℝ} (hr1 : 1 ≤ r) (hr2 : r ≤ 2)
    (hMoment : ∀ i ∈ s, Integrable (fun ω => |Z i ω| ^ r) P) :
    Integrable
      (fun z : Ω × (ι → Bool) =>
        |∑ i ∈ s, (if z.2 i then (1 : ℝ) else -1) * Z i z.1| ^ r)
      (P.prod (Measure.pi (fun _ : ι => (PMF.uniformOfFintype Bool).toMeasure))) ∧
    (∫ z : Ω × (ι → Bool),
        |∑ i ∈ s, (if z.2 i then (1 : ℝ) else -1) * Z i z.1| ^ r
      ∂P.prod (Measure.pi (fun _ : ι => (PMF.uniformOfFintype Bool).toMeasure))) ≤
      ∑ i ∈ s, ∫ ω, |Z i ω| ^ r ∂P := by
  classical
  let ν : Measure (ι → Bool) :=
    Measure.pi (fun _ : ι => (PMF.uniformOfFintype Bool).toMeasure)
  let S : Ω × (ι → Bool) → ℝ := fun z =>
    ∑ i ∈ s, (if z.2 i then (1 : ℝ) else -1) * Z i z.1
  let F : Ω × (ι → Bool) → ℝ := fun z => |S z| ^ r
  have hr0 : 0 ≤ r := le_trans (by norm_num : (0 : ℝ) ≤ 1) hr1
  have hsign (i : ι) :
      Measurable (fun ε : ι → Bool => if ε i then (1 : ℝ) else -1) := by
    exact measurable_of_countable _
  have hS : Measurable S := by
    dsimp only [S]
    apply Finset.measurable_sum
    intro i hi
    exact ((hsign i).comp measurable_snd).mul ((hZ i hi).comp measurable_fst)
  have hF : Measurable F :=
    (Real.continuous_rpow_const hr0).measurable.comp
      (_root_.continuous_abs.measurable.comp hS)
  have hSection (ε : ι → Bool) : Integrable (fun ω => F (ω, ε)) P := by
    let X : ι → Ω → ℝ := fun i ω =>
      (if ε i then (1 : ℝ) else -1) * Z i ω
    have hX : ∀ i ∈ s, Measurable (X i) := by
      intro i hi
      exact measurable_const.mul (hZ i hi)
    have hXMoment : ∀ i ∈ s, Integrable (fun ω => |X i ω| ^ r) P := by
      intro i hi
      by_cases hε : ε i
      · simpa [X, hε] using hMoment i hi
      · simpa [X, hε] using hMoment i hi
    have hsum := integrable_sum_and_abs_rpow_of_moments P s X hX hr1 hXMoment
    simpa [F, S, X] using hsum.2
  have hProduct : Integrable F (P.prod ν) := by
    apply (integrable_prod_iff' hF.aestronglyMeasurable).2
    exact ⟨Filter.Eventually.of_forall hSection, Integrable.of_finite⟩
  refine ⟨?_, ?_⟩
  · simpa only [F, S, ν] using hProduct
  · have hAverage : Integrable (fun ω => ∫ ε, F (ω, ε) ∂ν) P :=
      hProduct.integral_prod_left
    have hMomentSum : Integrable (fun ω => ∑ i ∈ s, |Z i ω| ^ r) P :=
      integrable_finsetSum s hMoment
    have hFiberBound (ω : Ω) :
        (∫ ε, F (ω, ε) ∂ν) ≤ ∑ i ∈ s, |Z i ω| ^ r := by
      simpa only [F, S, ν] using
        (integrable_and_integral_abs_rpow_sum_fair_sign_le s
          (fun i => Z i ω) (lt_of_lt_of_le zero_lt_one hr1) hr2).2
    calc
      (∫ z, F z ∂P.prod ν) = ∫ ω, ∫ ε, F (ω, ε) ∂ν ∂P :=
        integral_prod F hProduct
      _ ≤ ∫ ω, ∑ i ∈ s, |Z i ω| ^ r ∂P :=
        integral_mono hAverage hMomentSum hFiberBound
      _ = ∑ i ∈ s, ∫ ω, |Z i ω| ^ r ∂P :=
        integral_finsetSum s hMoment

end LPPDifferentiability
