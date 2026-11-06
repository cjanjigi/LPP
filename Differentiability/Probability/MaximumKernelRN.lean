/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Differentiability.Probability.MaximumModifiedFieldLaw
import Differentiability.Probability.MaximumRegionalDensity
import ProbabilityBasics.Probability.WithDensityEventBound

/-!
# The actual maximum-kernel density and event bound

This file proves the Radon–Nikodym formula and square-moment consequences for
maximum resampling on a finite region of the actual iid environment.

## Main results

- `maximum_kernel_map_eq_withDensity`: the maximum-modification map has the
  actual regional product density on the original environment law.
- `maximum_kernel_map_absolutelyContinuous` and
  `rnDeriv_maximum_kernel_map_ae`: absolute continuity and the actual
  Radon–Nikodym derivative formula.
- `integrable_sq_toReal_rnDeriv_maximum_kernel_map` and
  `integral_sq_toReal_rnDeriv_maximum_kernel_map_le`: genuine square
  integrability and the exact exponential cost.
- `maximum_kernel_map_event_bound`: the resulting bound for every measurable
  event.

The factors use both closed and open lower rays, so the formula includes
atomic probability laws. No moment, support, or atomlessness hypothesis is
used.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace LPPDifferentiability

/-- The maximum-resampling map has the regional product density on its original
iid environment law. -/
theorem maximum_kernel_map_eq_withDensity (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {δ : ℝ} (hδ : δ ∈ Icc (0 : ℝ) 1) (R : Finset Lattice) :
    Measure.map
        (fun p : (Environment × Environment) × (Lattice → Bool) =>
          fun v =>
            if v ∈ R ∧ p.2 v = true then max (p.1.1 v) (p.1.2 v) else p.1.1 v)
        (((environmentLaw μ).prod (environmentLaw μ)).prod
          (Measure.infinitePi (fun _ : Lattice =>
            ENNReal.ofReal (1 - δ) • Measure.dirac false +
              ENNReal.ofReal δ • Measure.dirac true))) =
      (environmentLaw μ).withDensity (fun ω : Environment =>
        ENNReal.ofReal
          (∏ v ∈ R, (1 - δ + δ * (μ.real (Iic (ω v)) + μ.real (Iio (ω v)))))) := by
  calc
    Measure.map
        (fun p : (Environment × Environment) × (Lattice → Bool) =>
          fun v =>
            if v ∈ R ∧ p.2 v = true then max (p.1.1 v) (p.1.2 v) else p.1.1 v)
        (((environmentLaw μ).prod (environmentLaw μ)).prod
          (Measure.infinitePi (fun _ : Lattice =>
            ENNReal.ofReal (1 - δ) • Measure.dirac false +
              ENNReal.ofReal δ • Measure.dirac true))) =
        Measure.infinitePi (fun v : Lattice => if v ∈ R then
          μ.withDensity (fun t => ENNReal.ofReal
            (1 - δ + δ * (μ.real (Iic t) + μ.real (Iio t)))) else μ) :=
      maximum_modification_map_eq_density_product μ hδ R
    _ = (environmentLaw μ).withDensity (fun ω : Environment =>
          ∏ v ∈ R, ENNReal.ofReal
            (1 - δ + δ * (μ.real (Iic (ω v)) + μ.real (Iio (ω v))))) :=
      infinitePi_maximum_regional_withDensity μ hδ R
    _ = (environmentLaw μ).withDensity (fun ω : Environment =>
          ENNReal.ofReal
            (∏ v ∈ R, (1 - δ + δ * (μ.real (Iic (ω v)) + μ.real (Iio (ω v)))))) := by
      congr 1
      funext ω
      exact (ENNReal.ofReal_prod_of_nonneg fun v hv =>
        (maximum_regional_density_mem_Icc μ hδ (ω v)).1).symm

/-- The actual maximum-resampling output law is absolutely continuous with
respect to the original environment law, even when a regional factor vanishes. -/
theorem maximum_kernel_map_absolutelyContinuous (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {δ : ℝ} (hδ : δ ∈ Icc (0 : ℝ) 1)
    (R : Finset Lattice) :
    Measure.map
        (fun p : (Environment × Environment) × (Lattice → Bool) =>
          fun v =>
            if v ∈ R ∧ p.2 v = true then max (p.1.1 v) (p.1.2 v) else p.1.1 v)
        (((environmentLaw μ).prod (environmentLaw μ)).prod
          (Measure.infinitePi (fun _ : Lattice =>
            ENNReal.ofReal (1 - δ) • Measure.dirac false +
              ENNReal.ofReal δ • Measure.dirac true))) ≪ environmentLaw μ := by
  rw [maximum_kernel_map_eq_withDensity μ hδ R]
  exact withDensity_absolutelyContinuous _ _

/-- The actual output law has the stated regional product as its
Radon–Nikodym derivative almost everywhere. -/
theorem rnDeriv_maximum_kernel_map_ae (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {δ : ℝ} (hδ : δ ∈ Icc (0 : ℝ) 1) (R : Finset Lattice) :
    (Measure.map
        (fun p : (Environment × Environment) × (Lattice → Bool) =>
          fun v =>
            if v ∈ R ∧ p.2 v = true then max (p.1.1 v) (p.1.2 v) else p.1.1 v)
        (((environmentLaw μ).prod (environmentLaw μ)).prod
          (Measure.infinitePi (fun _ : Lattice =>
            ENNReal.ofReal (1 - δ) • Measure.dirac false +
              ENNReal.ofReal δ • Measure.dirac true)))).rnDeriv (environmentLaw μ) =ᵐ[
                environmentLaw μ]
      (fun ω : Environment => ENNReal.ofReal
        (∏ v ∈ R, (1 - δ + δ * (μ.real (Iic (ω v)) + μ.real (Iio (ω v)))))) := by
  have hΦ : Measurable (fun ω : Environment =>
      ∏ v ∈ R, (1 - δ + δ * (μ.real (Iic (ω v)) + μ.real (Iio (ω v))))) :=
    Finset.measurable_prod R fun v _ =>
      (measurable_maximum_regional_density μ δ).comp (measurable_pi_apply v)
  rw [maximum_kernel_map_eq_withDensity μ hδ R]
  exact Measure.rnDeriv_withDensity (environmentLaw μ)
    (ENNReal.measurable_ofReal.comp hΦ)

/-- The square of the actual Radon–Nikodym derivative, converted to a real,
is integrable under the original environment law. -/
theorem integrable_sq_toReal_rnDeriv_maximum_kernel_map (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {δ : ℝ} (hδ : δ ∈ Icc (0 : ℝ) 1)
    (R : Finset Lattice) :
    Integrable
      (fun ω : Environment =>
        ((Measure.map
          (fun p : (Environment × Environment) × (Lattice → Bool) =>
            fun v =>
              if v ∈ R ∧ p.2 v = true then max (p.1.1 v) (p.1.2 v) else p.1.1 v)
          (((environmentLaw μ).prod (environmentLaw μ)).prod
            (Measure.infinitePi (fun _ : Lattice =>
              ENNReal.ofReal (1 - δ) • Measure.dirac false +
                ENNReal.ofReal δ • Measure.dirac true)))).rnDeriv
          (environmentLaw μ) ω).toReal ^ 2)
      (environmentLaw μ) := by
  have hRN := rnDeriv_maximum_kernel_map_ae μ hδ R
  have hnonneg : ∀ ω : Environment, 0 ≤
      ∏ v ∈ R, (1 - δ + δ * (μ.real (Iic (ω v)) + μ.real (Iio (ω v)))) :=
    fun ω => Finset.prod_nonneg fun v hv =>
      (maximum_regional_density_mem_Icc μ hδ (ω v)).1
  have htoReal :
      (fun ω : Environment =>
        ((Measure.map
          (fun p : (Environment × Environment) × (Lattice → Bool) =>
            fun v =>
              if v ∈ R ∧ p.2 v = true then max (p.1.1 v) (p.1.2 v) else p.1.1 v)
          (((environmentLaw μ).prod (environmentLaw μ)).prod
            (Measure.infinitePi (fun _ : Lattice =>
              ENNReal.ofReal (1 - δ) • Measure.dirac false +
                ENNReal.ofReal δ • Measure.dirac true)))).rnDeriv
          (environmentLaw μ) ω).toReal) =ᵐ[environmentLaw μ]
        (fun ω : Environment =>
          ∏ v ∈ R, (1 - δ + δ * (μ.real (Iic (ω v)) + μ.real (Iio (ω v))))) := by
    filter_upwards [hRN] with ω hω
    rw [hω]
    exact ENNReal.toReal_ofReal (hnonneg ω)
  have htoRealSq :
      (fun ω : Environment =>
        ((Measure.map
          (fun p : (Environment × Environment) × (Lattice → Bool) =>
            fun v =>
              if v ∈ R ∧ p.2 v = true then max (p.1.1 v) (p.1.2 v) else p.1.1 v)
          (((environmentLaw μ).prod (environmentLaw μ)).prod
            (Measure.infinitePi (fun _ : Lattice =>
              ENNReal.ofReal (1 - δ) • Measure.dirac false +
                ENNReal.ofReal δ • Measure.dirac true)))).rnDeriv
          (environmentLaw μ) ω).toReal ^ 2) =ᵐ[environmentLaw μ]
        (fun ω : Environment =>
          ((∏ v ∈ R, (1 - δ + δ * (μ.real (Iic (ω v)) + μ.real (Iio (ω v))))) ^ 2)) := by
    filter_upwards [htoReal] with ω hω
    rw [hω]
  have hprod : Integrable
      (fun ω : Environment =>
        ((∏ v ∈ R, (1 - δ + δ * (μ.real (Iic (ω v)) + μ.real (Iio (ω v))))) ^ 2))
      (environmentLaw μ) := integrable_sq_maximum_regional_product_density μ hδ R
  exact (integrable_congr htoRealSq).2 hprod

/-- The actual square moment of the real Radon–Nikodym derivative is at most
`exp (3 δ² |R|)`. -/
theorem integral_sq_toReal_rnDeriv_maximum_kernel_map_le (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {δ : ℝ} (hδ : δ ∈ Icc (0 : ℝ) 1)
    (R : Finset Lattice) :
    (∫ ω : Environment,
      ((Measure.map
        (fun p : (Environment × Environment) × (Lattice → Bool) =>
          fun v =>
            if v ∈ R ∧ p.2 v = true then max (p.1.1 v) (p.1.2 v) else p.1.1 v)
        (((environmentLaw μ).prod (environmentLaw μ)).prod
          (Measure.infinitePi (fun _ : Lattice =>
            ENNReal.ofReal (1 - δ) • Measure.dirac false +
              ENNReal.ofReal δ • Measure.dirac true)))).rnDeriv
        (environmentLaw μ) ω).toReal ^ 2 ∂environmentLaw μ) ≤
      Real.exp (3 * δ ^ 2 * R.card) := by
  have hRN := rnDeriv_maximum_kernel_map_ae μ hδ R
  have hnonneg : ∀ ω : Environment, 0 ≤
      ∏ v ∈ R, (1 - δ + δ * (μ.real (Iic (ω v)) + μ.real (Iio (ω v)))) :=
    fun ω => Finset.prod_nonneg fun v hv =>
      (maximum_regional_density_mem_Icc μ hδ (ω v)).1
  have htoRealSq :
      (fun ω : Environment =>
        ((Measure.map
          (fun p : (Environment × Environment) × (Lattice → Bool) =>
            fun v =>
              if v ∈ R ∧ p.2 v = true then max (p.1.1 v) (p.1.2 v) else p.1.1 v)
          (((environmentLaw μ).prod (environmentLaw μ)).prod
            (Measure.infinitePi (fun _ : Lattice =>
              ENNReal.ofReal (1 - δ) • Measure.dirac false +
                ENNReal.ofReal δ • Measure.dirac true)))).rnDeriv
          (environmentLaw μ) ω).toReal ^ 2) =ᵐ[environmentLaw μ]
        (fun ω : Environment =>
          ((∏ v ∈ R, (1 - δ + δ * (μ.real (Iic (ω v)) + μ.real (Iio (ω v))))) ^ 2)) := by
    filter_upwards [hRN] with ω hω
    rw [hω]
    rw [ENNReal.toReal_ofReal (hnonneg ω)]
  calc
    (∫ ω : Environment,
      ((Measure.map
        (fun p : (Environment × Environment) × (Lattice → Bool) =>
          fun v =>
            if v ∈ R ∧ p.2 v = true then max (p.1.1 v) (p.1.2 v) else p.1.1 v)
        (((environmentLaw μ).prod (environmentLaw μ)).prod
          (Measure.infinitePi (fun _ : Lattice =>
            ENNReal.ofReal (1 - δ) • Measure.dirac false +
              ENNReal.ofReal δ • Measure.dirac true)))).rnDeriv
        (environmentLaw μ) ω).toReal ^ 2 ∂environmentLaw μ) =
        ∫ ω : Environment,
          (∏ v ∈ R,
            (1 - δ + δ * (μ.real (Iic (ω v)) + μ.real (Iio (ω v))))) ^ 2
          ∂environmentLaw μ := integral_congr_ae htoRealSq
    _ ≤ Real.exp (3 * δ ^ 2 * R.card) :=
      integral_sq_maximum_regional_product_density_le μ hδ R

/-- The actual maximum-resampling output law satisfies the Cauchy–Schwarz event
bound for every measurable event. -/
theorem maximum_kernel_map_event_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {δ : ℝ} (hδ : δ ∈ Icc (0 : ℝ) 1) (R : Finset Lattice)
    {A : Set Environment} (hA : MeasurableSet A) :
    (Measure.map
        (fun p : (Environment × Environment) × (Lattice → Bool) =>
          fun v =>
            if v ∈ R ∧ p.2 v = true then max (p.1.1 v) (p.1.2 v) else p.1.1 v)
        (((environmentLaw μ).prod (environmentLaw μ)).prod
          (Measure.infinitePi (fun _ : Lattice =>
            ENNReal.ofReal (1 - δ) • Measure.dirac false +
              ENNReal.ofReal δ • Measure.dirac true)))).real A ≤
      Real.exp ((3 / 2 : ℝ) * δ ^ 2 * R.card) *
        Real.sqrt ((environmentLaw μ).real A) := by
  rw [maximum_kernel_map_eq_withDensity μ hδ R]
  have hcost := integral_sq_maximum_regional_product_density_le μ hδ R
  have hbound := withDensity_event_bound_of_integral_sq_le
    (environmentLaw μ)
    (fun ω : Environment =>
      ∏ v ∈ R, (1 - δ + δ * (μ.real (Iic (ω v)) + μ.real (Iio (ω v)))) )
    (Finset.measurable_prod R fun v _ =>
      (measurable_maximum_regional_density μ δ).comp (measurable_pi_apply v))
    (fun ω => Finset.prod_nonneg fun v hv =>
      (maximum_regional_density_mem_Icc μ hδ (ω v)).1)
    (integrable_sq_maximum_regional_product_density μ hδ R)
    (3 * δ ^ 2 * R.card) hcost hA
  calc
    ((environmentLaw μ).withDensity fun ω : Environment =>
      ENNReal.ofReal
        (∏ v ∈ R, (1 - δ + δ * (μ.real (Iic (ω v)) + μ.real (Iio (ω v)))))).real A ≤
      Real.exp ((3 * δ ^ 2 * R.card) / 2) *
        Real.sqrt ((environmentLaw μ).real A) := hbound
    _ = Real.exp ((3 / 2 : ℝ) * δ ^ 2 * R.card) *
        Real.sqrt ((environmentLaw μ).real A) := by
      congr 1
      ring

end LPPDifferentiability
