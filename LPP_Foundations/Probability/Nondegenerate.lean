/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Nondegeneracy of a real probability law

A real probability law is nondegenerate when no single value carries all of the probability. This is
equivalent to the identity random variable not being almost surely constant. These equivalences
need no moment assumptions.
-/

public section

open MeasureTheory

namespace LPPDifferentiability

/-- A real probability law gives a singleton mass one exactly when it is almost surely constant
at that singleton's value. -/
theorem measure_singleton_eq_one_iff_ae_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] (c : ℝ) :
    μ ({c} : Set ℝ) = 1 ↔ ∀ᵐ x ∂μ, x = c := by
  change μ ({c} : Set ℝ) = 1 ↔ {x : ℝ | x = c} ∈ ae μ
  rw [Set.ofPred_eq_eq_singleton]
  exact (mem_ae_iff_prob_eq_one (μ := μ) (measurableSet_singleton c)).symm

/-- Excluding singleton mass one excludes every almost sure constant value. -/
theorem forall_measure_singleton_ne_one_iff_not_exists_ae_eq
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (∀ c : ℝ, μ ({c} : Set ℝ) ≠ 1) ↔ ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, x = c := by
  constructor
  · rintro h ⟨c, hc⟩
    exact h c ((measure_singleton_eq_one_iff_ae_eq μ c).mpr hc)
  · intro h c hc
    exact h ⟨c, (measure_singleton_eq_one_iff_ae_eq μ c).mp hc⟩

/-- The singleton hypothesis used for nondegeneracy is equivalent to absence of an almost sure
constant value, without a variance or moment hypothesis. -/
theorem forall_measure_singleton_lt_one_iff_not_exists_ae_eq
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (∀ c : ℝ, μ ({c} : Set ℝ) < 1) ↔ ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, x = c := by
  rw [← forall_measure_singleton_ne_one_iff_not_exists_ae_eq μ]
  constructor
  · intro h c
    exact (h c).ne
  · intro h c
    exact lt_of_le_of_ne prob_le_one (h c)

end LPPDifferentiability
