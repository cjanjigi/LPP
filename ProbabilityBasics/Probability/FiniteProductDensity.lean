/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Densities on a finite product

This file treats densities that are products of one-site factors on a finite product of
probability spaces. Each factor is a measurable function with values in `[0, 2]`. The bound on
the one-site second moment of each factor is a hypothesis here, not a result of this file.
-/

public section

open MeasureTheory

namespace LPPDifferentiability

variable {ι : Type*} [Fintype ι]

private theorem integrable_factor_of_bounds (μ : Measure ℝ) [IsFiniteMeasure μ]
    (f : ℝ → ℝ) (hf : Measurable f) (h0 : ∀ x, 0 ≤ f x) (h2 : ∀ x, f x ≤ 2) :
    Integrable f μ := by
  refine (integrable_const (2 : ℝ)).mono' hf.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (h0 x)]
    exact h2 x)

private theorem integrable_factor_sq_of_bounds (μ : Measure ℝ) [IsFiniteMeasure μ]
    (f : ℝ → ℝ) (hf : Measurable f) (h0 : ∀ x, 0 ≤ f x) (h2 : ∀ x, f x ≤ 2) :
    Integrable (fun x => (f x) ^ 2) μ := by
  refine (integrable_const (4 : ℝ)).mono' (hf.pow_const 2).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith only [h0 x, h2 x])

/-- Bounded real factors give finite weighted marginal measures. -/
theorem isFiniteMeasure_withDensity_factor (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f : ℝ → ℝ) (hf : Measurable f) (h0 : ∀ x, 0 ≤ f x) (h2 : ∀ x, f x ≤ 2) :
    IsFiniteMeasure (μ.withDensity (fun x => ENNReal.ofReal (f x))) :=
  isFiniteMeasure_withDensity_ofReal (integrable_factor_of_bounds μ f hf h0 h2).2

/-- The product of the weighted one-site marginals is the measure with the product density. -/
theorem pi_withDensity_factors (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (f : ι → ℝ → ℝ) (hf : ∀ i, Measurable (f i))
    (h0 : ∀ i x, 0 ≤ f i x) (h2 : ∀ i x, f i x ≤ 2) :
    Measure.pi (fun i => (μ i).withDensity (fun x => ENNReal.ofReal (f i x))) =
      (Measure.pi μ).withDensity (fun x => ∏ i, ENNReal.ofReal (f i (x i))) := by
  classical
  let : ∀ i, IsFiniteMeasure ((μ i).withDensity (fun x => ENNReal.ofReal (f i x))) :=
    fun i => isFiniteMeasure_withDensity_factor (μ i) (f i) (hf i) (h0 i) (h2 i)
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi]
  have hi : ∀ i, Integrable (f i) ((μ i).restrict (s i)) :=
    fun i => (integrable_factor_of_bounds (μ i) (f i) (hf i) (h0 i) (h2 i)).restrict
  have hp : Integrable (fun x : ι → ℝ => ∏ i, f i (x i))
      (Measure.pi (fun i => (μ i).restrict (s i))) := Integrable.fintype_prod hi
  calc
    (∫⁻ x, ∏ i, ENNReal.ofReal (f i (x i))
        ∂Measure.pi (fun i => (μ i).restrict (s i))) =
        ENNReal.ofReal (∫ x : ι → ℝ, ∏ i, f i (x i)
          ∂Measure.pi (fun i => (μ i).restrict (s i))) := by
      simp_rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => h0 i _)]
      exact (ofReal_integral_eq_lintegral_ofReal hp
        (Filter.Eventually.of_forall (fun x => Finset.prod_nonneg (fun i _ => h0 i (x i))))).symm
    _ = ENNReal.ofReal (∏ i, ∫ x, f i x ∂(μ i).restrict (s i)) := by
      rw [integral_fintype_prod_eq_prod]
    _ = ∏ i, ENNReal.ofReal (∫ x, f i x ∂(μ i).restrict (s i)) :=
      ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (h0 i))
    _ = ∏ i, (μ i).withDensity (fun x => ENNReal.ofReal (f i x)) (s i) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [withDensity_apply _ (hs i)]
      exact ofReal_integral_eq_lintegral_ofReal (hi i)
        (Filter.Eventually.of_forall (h0 i))

/-- The square of the real product density is integrable. -/
theorem integrable_sq_prod_factors (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (f : ι → ℝ → ℝ) (hf : ∀ i, Measurable (f i))
    (h0 : ∀ i x, 0 ≤ f i x) (h2 : ∀ i x, f i x ≤ 2) :
    Integrable (fun x : ι → ℝ => (∏ i, f i (x i)) ^ 2) (Measure.pi μ) := by
  have hi := Integrable.fintype_prod (fun i =>
    integrable_factor_sq_of_bounds (μ i) (f i) (hf i) (h0 i) (h2 i))
  simpa only [Finset.prod_pow] using hi

/-- Fubini's theorem factors the second moment of a finite product, with no product identity
assumed. -/
theorem integral_sq_prod_factors (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (f : ι → ℝ → ℝ) :
    (∫ x : ι → ℝ, (∏ i, f i (x i)) ^ 2 ∂Measure.pi μ) =
      ∏ i, ∫ x, (f i x) ^ 2 ∂μ i := by
  simp_rw [← Finset.prod_pow]
  exact integral_fintype_prod_eq_prod (fun i x => (f i x) ^ 2)

/-- If the second moment of each one-site factor is at most `exp (3 δ^2)`, then the second moment
of the product density is at most `exp (3 δ^2 * card ι)`. The one-site bound is a hypothesis of
this lemma, not something it proves. -/
theorem integral_sq_prod_factors_le_exp (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (f : ι → ℝ → ℝ)
    (hf : ∀ i, Measurable (f i)) (h0 : ∀ i x, 0 ≤ f i x) (h2 : ∀ i x, f i x ≤ 2)
    (δ : ℝ)
    (hcost : ∀ i, (∫ x, (f i x) ^ 2 ∂μ i) ≤ Real.exp (3 * δ ^ 2)) :
    (∫ x : ι → ℝ, (∏ i, f i (x i)) ^ 2 ∂Measure.pi μ) ≤
      Real.exp (3 * δ ^ 2 * Fintype.card ι) := by
  have hi := Integrable.fintype_prod (fun i =>
    integrable_factor_sq_of_bounds (μ i) (f i) (hf i) (h0 i) (h2 i))
  calc
    (∫ x : ι → ℝ, (∏ i, f i (x i)) ^ 2 ∂Measure.pi μ) ≤
        ∫ x : ι → ℝ, ∏ i, (f i (x i)) ^ 2 ∂Measure.pi μ := by
      apply integral_mono (integrable_sq_prod_factors μ f hf h0 h2) hi
      intro x
      exact (Finset.prod_pow Finset.univ 2 (fun i => f i (x i))).symm.le
    _ = ∏ i, ∫ x, (f i x) ^ 2 ∂μ i :=
      integral_fintype_prod_eq_prod (fun i x => (f i x) ^ 2)
    _ ≤ ∏ _i : ι, Real.exp (3 * δ ^ 2) := by
      exact Finset.prod_le_prod₀ (fun i _ => integral_nonneg (fun x => sq_nonneg (f i x)))
        (fun i _ => hcost i)
    _ = Real.exp (3 * δ ^ 2 * Fintype.card ι) := by
      rw [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul, mul_comm]

end LPPDifferentiability
