/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.UniformOriginIncrements
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-!
# Joint laws of the random-origin increments

This gives the finite probability laws in equation (2.13) of Liggett (1985). The
origin `j + 1` of the original sequence is represented by the index `j`; every
original index is positive.
-/

public section

open MeasureTheory BoundedContinuousFunction

namespace LPPDifferentiability

/-- The full increment sequence viewed from positive origin `j+1`. -/
@[expose] def originIncrementSequence {Ω : Type*} (X : ℕ → Ω → ℝ) (j : ℕ)
    (ω : Ω) (k : ℕ) : ℝ := X (k + j + 2) ω - X (k + j + 1) ω

theorem measurable_originIncrementSequence {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (hm : ∀ j, 0 < j → Measurable (X j)) (j : ℕ) :
    Measurable (originIncrementSequence X j) :=
  Measurable.of_eval fun k => (hm _ (by omega)).sub (hm _ (by omega))

theorem measurable_uniformOriginIncrement_sequence {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (hm : ∀ j, 0 < j → Measurable (X j)) (n : ℕ) :
    Measurable (fun p : Ω × Fin (n + 1) =>
      fun k => uniformOriginIncrement X n k p) :=
  Measurable.of_eval fun k => measurable_uniformOriginIncrement X hm n k

/-- The joint law under the independent finite uniform-origin product. -/
@[expose] noncomputable def uniformOriginIncrementLaw {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hm : ∀ j, 0 < j → Measurable (X j)) (n : ℕ) :
    ProbabilityMeasure (ℕ → ℝ) :=
  ⟨(uniformOriginProduct μ n).map
    (fun p => fun k => uniformOriginIncrement X n k p),
    (Measure.isProbabilityMeasure_map_iff
      (measurable_uniformOriginIncrement_sequence X hm n).aemeasurable).2 inferInstance⟩

theorem uniformOriginIncrementLaw_toMeasure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hm : ∀ j, 0 < j → Measurable (X j)) (n : ℕ) :
    (uniformOriginIncrementLaw μ X hm n : Measure (ℕ → ℝ)) =
      (uniformOriginProduct μ n).map
        (fun p => fun k => uniformOriginIncrement X n k p) := rfl

private theorem integrable_test_origin {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hm : ∀ j, 0 < j → Measurable (X j)) (j : ℕ)
    (f : (ℕ → ℝ) →ᵇ ℝ) :
    Integrable (fun ω => f (originIncrementSequence X j ω)) μ :=
  (integrable_const ‖f‖).mono'
    (f.continuous.measurable.comp (measurable_originIncrementSequence X hm j)).aestronglyMeasurable
    (ae_of_all _ fun _ω => f.norm_coe_le_norm _)

/-- The exact finite-average identity for test functions, before the limit in
equation (2.13) of Liggett (1985). -/
theorem integral_uniformOriginIncrementLaw {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hm : ∀ j, 0 < j → Measurable (X j)) (n : ℕ)
    (f : (ℕ → ℝ) →ᵇ ℝ) :
    (∫ z, f z ∂(uniformOriginIncrementLaw μ X hm n : Measure (ℕ → ℝ))) =
      (∑ u : Fin (n + 1), ∫ ω, f (originIncrementSequence X u.val ω) ∂μ) /
        (n + 1 : ℝ) := by
  rw [uniformOriginIncrementLaw_toMeasure,
    integral_map (measurable_uniformOriginIncrement_sequence X hm n).aemeasurable
      f.continuous.measurable.aestronglyMeasurable]
  exact integral_uniformOrigin_family μ n
    (fun u ω => f (originIncrementSequence X u.val ω))
    (fun u => f.continuous.measurable.comp (measurable_originIncrementSequence X hm u.val))
    (fun u => integrable_test_origin μ X hm u.val f)

end LPPDifferentiability
