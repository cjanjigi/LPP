/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Differentiability.Probability.MaximumLawDensity

/-!
# The one-site maximum-resampling law

A Bernoulli coordinate chooses between retaining the original sample and
replacing it by its maximum with an independent sample. This is the one-site
mixture in Lemma 4.1(i) of the differentiability preprint. Its density and
second-moment bound are proved here.

## References

- C. Janjigian, F. Rassoul-Agha and T. Seppäläinen,
  *Differentiability of the shape function in the planar corner growth model*, preprint.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace LPPDifferentiability

/-- The literal two-point Bool law with Bernoulli parameter `δ` is a probability. -/
theorem maximum_resampling_coin_is_probability {δ : ℝ} (hδ : δ ∈ Icc (0 : ℝ) 1) :
    IsProbabilityMeasure
      (ENNReal.ofReal (1 - δ) • Measure.dirac false +
        ENNReal.ofReal δ • Measure.dirac true) := by
  constructor
  have hδ0 : 0 ≤ δ := hδ.1
  have hδ1 : δ ≤ 1 := hδ.2
  have h0 : 0 ≤ 1 - δ := sub_nonneg.mpr hδ1
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (mem_univ false),
    Measure.dirac_apply_of_mem (mem_univ true)]
  simp only [smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add h0 hδ0]
  norm_num [sub_add_cancel]

/-- A maximum-resampling output is at least its original sample in every case. -/
theorem maximum_resampling_output_ge_original (x y : ℝ) (b : Bool) :
    x ≤ if b then max x y else x := by
  cases b with
  | false => exact le_rfl
  | true => exact le_max_left x y

/-- The actual product map has the source's weighted one-site mixture law. -/
theorem maximum_resampling_map_eq_mixture (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {δ : ℝ} (_ : δ ∈ Icc (0 : ℝ) 1) :
    Measure.map (fun p : (ℝ × ℝ) × Bool =>
      if p.2 then max p.1.1 p.1.2 else p.1.1)
        ((μ.prod μ).prod
          (ENNReal.ofReal (1 - δ) • Measure.dirac false +
            ENNReal.ofReal δ • Measure.dirac true)) =
      ENNReal.ofReal (1 - δ) • μ +
        ENNReal.ofReal δ •
          Measure.map (fun p : ℝ × ℝ => max p.1 p.2) (μ.prod μ) := by
  classical
  let F : (ℝ × ℝ) × Bool → ℝ := fun p =>
    if p.2 then max p.1.1 p.1.2 else p.1.1
  let coin : Measure Bool :=
    ENNReal.ofReal (1 - δ) • Measure.dirac false + ENNReal.ofReal δ • Measure.dirac true
  have hcond : MeasurableSet {p : (ℝ × ℝ) × Bool | p.2 = true} := by
    change MeasurableSet (Prod.snd ⁻¹' ({true} : Set Bool))
    exact (measurableSet_singleton true).preimage measurable_snd
  have hF : Measurable F := by
    change Measurable (fun p : (ℝ × ℝ) × Bool =>
      if p.2 = true then max p.1.1 p.1.2 else p.1.1)
    exact Measurable.ite hcond (by fun_prop) (by fun_prop)
  have hfalse : Measure.map F ((μ.prod μ).prod (Measure.dirac false)) = μ := by
    rw [Measure.prod_dirac, Measure.map_map hF measurable_prodMk_right]
    change Measure.map Prod.fst (μ.prod μ) = μ
    simp
  have htrue : Measure.map F ((μ.prod μ).prod (Measure.dirac true)) =
      Measure.map (fun p : ℝ × ℝ => max p.1 p.2) (μ.prod μ) := by
    rw [Measure.prod_dirac, Measure.map_map hF measurable_prodMk_right]
    rfl
  change Measure.map F ((μ.prod μ).prod coin) = _
  rw [show coin =
    ENNReal.ofReal (1 - δ) • Measure.dirac false +
      ENNReal.ofReal δ • Measure.dirac true from rfl]
  rw [Measure.prod_add, Measure.prod_smul_right, Measure.prod_smul_right,
    Measure.map_add _ _ hF, Measure.map_smul _ hF.aemeasurable,
    Measure.map_smul _ hF.aemeasurable, hfalse, htrue]

/-- The literal product space for maximum resampling is a probability space. -/
theorem maximum_resampling_product_is_probability (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {δ : ℝ} (hδ : δ ∈ Icc (0 : ℝ) 1) :
    IsProbabilityMeasure
      ((μ.prod μ).prod
        (ENNReal.ofReal (1 - δ) • Measure.dirac false +
          ENNReal.ofReal δ • Measure.dirac true)) := by
  let coin : Measure Bool :=
    ENNReal.ofReal (1 - δ) • Measure.dirac false + ENNReal.ofReal δ • Measure.dirac true
  exact @Measure.prod.instIsProbabilityMeasure (ℝ × ℝ) Bool _ _ (μ.prod μ) coin
    (inferInstance : IsProbabilityMeasure (μ.prod μ))
    (maximum_resampling_coin_is_probability hδ)

/-- The actual maximum-resampling law has the literal affine density from Lemma 4.1(i) of the
differentiability preprint. -/
theorem maximum_resampling_map_eq_withDensity (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {δ : ℝ} (hδ : δ ∈ Icc (0 : ℝ) 1) :
    Measure.map (fun p : (ℝ × ℝ) × Bool =>
      if p.2 then max p.1.1 p.1.2 else p.1.1)
        ((μ.prod μ).prod
          (ENNReal.ofReal (1 - δ) • Measure.dirac false +
            ENNReal.ofReal δ • Measure.dirac true)) =
      μ.withDensity (fun t => ENNReal.ofReal
        (1 - δ + δ * (μ.real (Iic t) + μ.real (Iio t)))) := by
  classical
  have hδ0 : 0 ≤ δ := hδ.1
  have hδ1 : δ ≤ 1 := hδ.2
  have hweight0 : 0 ≤ 1 - δ := sub_nonneg.mpr hδ1
  let raw : ℝ → ℝ≥0∞ := fun t => μ (Iic t) + μ (Iio t)
  have hraw (t : ℝ) : raw t = ENNReal.ofReal (μ.real (Iic t) + μ.real (Iio t)) := by
    rw [ENNReal.ofReal_add measureReal_nonneg measureReal_nonneg,
      ofReal_measureReal, ofReal_measureReal]
  have hdensity (t : ℝ) :
      ENNReal.ofReal (1 - δ + δ * (μ.real (Iic t) + μ.real (Iio t))) =
        ENNReal.ofReal (1 - δ) + ENNReal.ofReal δ * raw t := by
    rw [ENNReal.ofReal_add hweight0 (mul_nonneg hδ0 (add_nonneg measureReal_nonneg measureReal_nonneg)),
      ENNReal.ofReal_mul hδ0, hraw]
  calc
    Measure.map (fun p : (ℝ × ℝ) × Bool =>
        if p.2 then max p.1.1 p.1.2 else p.1.1)
          ((μ.prod μ).prod
            (ENNReal.ofReal (1 - δ) • Measure.dirac false +
              ENNReal.ofReal δ • Measure.dirac true)) =
        ENNReal.ofReal (1 - δ) • μ +
          ENNReal.ofReal δ • Measure.map (fun p : ℝ × ℝ => max p.1 p.2) (μ.prod μ) :=
      maximum_resampling_map_eq_mixture μ hδ
    _ = ENNReal.ofReal (1 - δ) • μ + ENNReal.ofReal δ • μ.withDensity raw := by
      rw [map_max_eq_withDensity μ]
    _ = μ.withDensity (fun t => ENNReal.ofReal (1 - δ) + ENNReal.ofReal δ * raw t) := by
      rw [← withDensity_const, ← withDensity_smul' (ENNReal.ofReal δ) raw
        (ENNReal.ofReal_ne_top), ← withDensity_add_left measurable_const]
      congr 1
    _ = μ.withDensity (fun t => ENNReal.ofReal
        (1 - δ + δ * (μ.real (Iic t) + μ.real (Iio t)))) := by
      congr 1
      funext t
      exact (hdensity t).symm

/-- The actual resampling law is absolutely continuous with respect to its input law. -/
theorem maximum_resampling_map_absolutelyContinuous (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {δ : ℝ} (hδ : δ ∈ Icc (0 : ℝ) 1) :
    Measure.map (fun p : (ℝ × ℝ) × Bool =>
      if p.2 then max p.1.1 p.1.2 else p.1.1)
        ((μ.prod μ).prod
          (ENNReal.ofReal (1 - δ) • Measure.dirac false +
            ENNReal.ofReal δ • Measure.dirac true)) ≪ μ := by
  rw [maximum_resampling_map_eq_withDensity μ hδ]
  exact withDensity_absolutelyContinuous μ _

/-- The squared maximum-mixture density has the bound
`integral_maximum_mixture_density_sq_le`. -/
alias integral_maximum_resampling_density_sq_le := integral_maximum_mixture_density_sq_le

end LPPDifferentiability
