/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.MeasureTheory.Measure.Prod
public import Martin2004.Probability.AnimalLayerCake

/-!
# Expected layer-cake bounds for finite families

The expected maximum of the total weights in a finite nonempty family is
bounded by the positive-level integral of the expected strict-threshold
maximum. The integrals are `ENNReal`-valued, so no finite-moment assumption is
needed.
-/

public section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace LPPDifferentiability

/-- The expected maximum total weight is bounded by the positive-level
integral of the expected strict-threshold maximum. This statement keeps the
expectations extended-valued and does not assume that they are finite. -/
theorem expected_finite_animalWeightMaximum_le_lintegral_thresholdMaximum
    {Ω α : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [SFinite μ]
    (H : Finset (Finset α)) (hH : H.Nonempty) (w : Ω → α → ℝ)
    (hw_meas : ∀ v, Measurable (fun ω => w ω v))
    (hw_nonneg : ∀ ω v, 0 ≤ w ω v) :
    (∫⁻ ω, H.sup' hH (fun U => ∑ v ∈ U, ENNReal.ofReal (w ω v)) ∂μ) ≤
      ∫⁻ t in Ioi (0 : ℝ),
        ∫⁻ ω, animalThresholdMaximum H hH (fun v => w ω v) t ∂μ ∂volume := by
  classical
  have hpointwise (ω : Ω) :
      H.sup' hH (fun U => ∑ v ∈ U, ENNReal.ofReal (w ω v)) ≤
        ∫⁻ t in Ioi (0 : ℝ),
          animalThresholdMaximum H hH (fun v => w ω v) t ∂volume :=
    finite_animalThresholdMaximum_lintegral H hH (fun v => w ω v)
      (fun v => hw_nonneg ω v)
  have hjoint : Measurable (fun p : Ω × ℝ =>
      animalThresholdMaximum H hH (fun v => w p.1 v) p.2) :=
    measurable_animalThresholdMaximum H hH w hw_meas
  have hswap := lintegral_lintegral_swap
      (μ := μ) (ν := volume.restrict (Ioi (0 : ℝ)))
      (f := fun ω t => animalThresholdMaximum H hH (fun v => w ω v) t)
      (by exact hjoint.aemeasurable)
  exact (lintegral_mono hpointwise).trans_eq hswap

end LPPDifferentiability
