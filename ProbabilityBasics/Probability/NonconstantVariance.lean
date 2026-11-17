/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Moments.Variance

/-!
# Nonconstant laws have positive centered second moment

For a probability law with finite second moment, zero variance would make the coordinate equal to
its mean almost everywhere. Thus every nonconstant such law has positive centered second moment.
-/

public section

open MeasureTheory
open scoped ProbabilityTheory

namespace ProbabilityBasics

/-- A nonconstant probability law with finite second moment has positive centered second moment.
This is the positive-standard-deviation step used in Martin (2004), Theorem 2.4. -/
theorem integral_centered_sq_pos_of_not_ae_const
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h2 : Integrable (fun x : ℝ => x ^ 2) μ)
    (hnonconstant : ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, x = c) :
    0 < ∫ x, (x - ∫ y, y ∂μ) ^ 2 ∂μ := by
  have hXmem : MemLp (fun x : ℝ => x) 2 μ :=
    (memLp_two_iff_integrable_sq (by fun_prop)).2 h2
  have hvarianceNonneg :
      0 ≤ ProbabilityTheory.variance (fun x : ℝ => x) μ :=
    ProbabilityTheory.variance_nonneg _ _
  have hvarianceNeZero :
      ProbabilityTheory.variance (fun x : ℝ => x) μ ≠ 0 := by
    intro hvarianceZero
    apply hnonconstant
    refine ⟨∫ x : ℝ, x ∂μ, ?_⟩
    have hconstant :=
      ProbabilityTheory.ae_eq_integral_of_variance_eq_zero hXmem hvarianceZero
    simpa using hconstant
  have hvariancePos : 0 < ProbabilityTheory.variance (fun x : ℝ => x) μ :=
    lt_of_le_of_ne hvarianceNonneg (Ne.symm hvarianceNeZero)
  rw [← ProbabilityTheory.variance_eq_integral (X := fun x : ℝ => x) (μ := μ)
    measurable_id.aemeasurable]
  exact hvariancePos

end ProbabilityBasics
