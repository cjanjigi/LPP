/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Analysis.ERealPerturbation
public import ProbabilityBasics.Probability.SublinearBoundary
public import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Invariance of upper and lower orbit-average limits

The averages are Mathlib's literal finite Birkhoff averages. Their upper and
lower limits take values in EReal; finiteness is not assumed.
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace LPPDifferentiability

/-- The exact boundary difference of two shifted finite orbit averages. -/
theorem birkhoffAverage_shift_sub {Ω : Type*} (T : Ω → Ω) (f : Ω → ℝ)
    (n : ℕ) (ω : Ω) :
    birkhoffAverage ℝ T f n (T ω) - birkhoffAverage ℝ T f n ω =
      (f ((T^[n]) ω) - f ω) / (n : ℝ) := by
  simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using
    birkhoffAverage_apply_sub_birkhoffAverage (R := ℝ) T f n ω

/-- Under measure preservation, shifting an integrable orbit average changes it
by a quantity tending to zero almost surely. -/
theorem ae_tendsto_birkhoffAverage_shift_sub {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω} {f : Ω → ℝ}
    (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ =>
      birkhoffAverage ℝ T f n (T ω) - birkhoffAverage ℝ T f n ω) atTop (𝓝 0) := by
  filter_upwards [ae_tendsto_iterate_div_nat hT hf] with ω hω
  simpa only [birkhoffAverage_shift_sub, sub_div, sub_zero] using
    hω.sub (tendsto_const_div_atTop_nhds_zero_nat (f ω))

/-- The extended-real upper orbit-average limit is invariant almost surely. -/
theorem ae_limsup_birkhoffAverage_shift {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω} {f : Ω → ℝ}
    (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) :
    ∀ᵐ ω ∂μ,
      limsup (fun n => ((birkhoffAverage ℝ T f n (T ω) : ℝ) : EReal)) atTop =
        limsup (fun n => ((birkhoffAverage ℝ T f n ω : ℝ) : EReal)) atTop := by
  filter_upwards [ae_tendsto_birkhoffAverage_shift_sub hT hf] with ω hω
  exact limsup_coe_eq_of_tendsto_sub_zero hω

/-- The extended-real lower orbit-average limit is invariant almost surely. -/
theorem ae_liminf_birkhoffAverage_shift {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω} {f : Ω → ℝ}
    (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) :
    ∀ᵐ ω ∂μ,
      liminf (fun n => ((birkhoffAverage ℝ T f n (T ω) : ℝ) : EReal)) atTop =
        liminf (fun n => ((birkhoffAverage ℝ T f n ω : ℝ) : EReal)) atTop := by
  filter_upwards [ae_tendsto_birkhoffAverage_shift_sub hT hf] with ω hω
  exact liminf_coe_eq_of_tendsto_sub_zero hω

end LPPDifferentiability
