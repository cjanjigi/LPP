/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.AnimalLayerCake
public import LPP_Foundations.Probability.EnvironmentMap
public import Mathlib.Probability.Distributions.Bernoulli

/-!
# Strict threshold indicators

The threshold field uses the strict event `t < ω z`. It is a measurable,
independent zero-one field under the actual canonical environment law. Its
one-site success probability is the strict upper tail of the original weight
law, including when that law has atoms.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace LPPDifferentiability

/-- The real-valued indicator of the strict event that a value exceeds `t`. -/
noncomputable def strictThresholdIndicator (t x : ℝ) : ℝ := if t < x then 1 else 0

/-- The strict threshold indicator is the indicator of the open upper tail. -/
theorem strictThresholdIndicator_eq_indicator (t : ℝ) :
    strictThresholdIndicator t = (Ioi t).indicator (fun _ : ℝ => (1 : ℝ)) := by
  funext x
  by_cases h : t < x
  · simp [strictThresholdIndicator, mem_Ioi, h]
  · simp [strictThresholdIndicator, mem_Ioi, h]

/-- The strict threshold indicator is measurable. -/
theorem measurable_strictThresholdIndicator (t : ℝ) :
    Measurable (strictThresholdIndicator t) := by
  unfold strictThresholdIndicator
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
    measurable_const measurable_const

/-- A strict threshold indicator takes only the values zero and one. -/
theorem strictThresholdIndicator_zero_or_one (t x : ℝ) :
    strictThresholdIndicator t x = 0 ∨ strictThresholdIndicator t x = 1 := by
  by_cases h : t < x
  · simp [strictThresholdIndicator, h]
  · simp [strictThresholdIndicator, h]

/-- The indicator equals one exactly on the strict upper tail. -/
theorem strictThresholdIndicator_one_iff (t x : ℝ) :
    strictThresholdIndicator t x = 1 ↔ t < x := by
  simp [strictThresholdIndicator]

/-- The strict upper-tail probability is a member of the unit interval. -/
theorem strictThresholdProbability_mem_unitInterval (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (t : ℝ) :
    μ.real (Ioi t) ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨measureReal_nonneg, measureReal_le_one⟩

/-- The strict threshold indicator has the Bernoulli law with its actual
one-event probability under the original one-site measure. -/
theorem strictThresholdIndicator_hasLaw (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (t : ℝ) :
    HasLaw (strictThresholdIndicator t)
      (bernoulliMeasure (1 : ℝ) 0 ⟨μ.real (Ioi t), by simp⟩) μ := by
  rw [strictThresholdIndicator_eq_indicator]
  exact hasLaw_indicator_one_bernoulliMeasure
    (s := Ioi t) measurableSet_Ioi.nullMeasurableSet

/-- The actual real-valued strict threshold field on the canonical environment. -/
noncomputable def strictThresholdField (t : ℝ) (ω : Environment) : Environment :=
  fun z => strictThresholdIndicator t (ω z)

/-- The strict threshold field is measurable as an environment-valued map. -/
theorem measurable_strictThresholdField (t : ℝ) :
    Measurable (strictThresholdField t) := by
  exact measurable_coordinatewise_environment_map (strictThresholdIndicator t)
    (measurable_strictThresholdIndicator t)

/-- Evaluation of the strict threshold field at a fixed site is measurable. -/
theorem measurable_strictThresholdField_eval (t : ℝ) (z : Lattice) :
    Measurable (fun ω : Environment => strictThresholdField t ω z) := by
  exact (measurable_environment_eval z).comp (measurable_strictThresholdField t)

/-- Every value of the strict threshold field is zero or one. -/
theorem strictThresholdField_zero_or_one (t : ℝ) (ω : Environment) (z : Lattice) :
    strictThresholdField t ω z = 0 ∨ strictThresholdField t ω z = 1 := by
  exact strictThresholdIndicator_zero_or_one t (ω z)

/-- The strict threshold coordinates are jointly independent under the actual
canonical environment law. -/
theorem iIndepFun_strictThresholdField_eval (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (t : ℝ) :
    iIndepFun (fun z (ω : Environment) => strictThresholdField t ω z)
      (environmentLaw μ) := by
  simpa [strictThresholdField] using
    iIndepFun_coordinatewise_environment_eval μ (strictThresholdIndicator t)
      (measurable_strictThresholdIndicator t)

/-- Each actual threshold coordinate has the Bernoulli law with common
success probability `μ.real (Ioi t)`. -/
theorem hasLaw_strictThresholdField_eval (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (t : ℝ) (z : Lattice) :
    HasLaw (fun ω : Environment => strictThresholdField t ω z)
      (bernoulliMeasure (1 : ℝ) 0 ⟨μ.real (Ioi t), by simp⟩)
      (environmentLaw μ) := by
  refine ⟨(measurable_strictThresholdField_eval t z).aemeasurable, ?_⟩
  calc
    (environmentLaw μ).map (fun ω : Environment => strictThresholdField t ω z) =
        (environmentLaw μ).map
          (fun ω : Environment => strictThresholdIndicator t (ω z)) := rfl
    _ = μ.map (strictThresholdIndicator t) :=
      environmentLaw_map_coordinatewise_eval μ (strictThresholdIndicator t)
        (measurable_strictThresholdIndicator t) z
    _ = bernoulliMeasure (1 : ℝ) 0 ⟨μ.real (Ioi t), by simp⟩ :=
      (strictThresholdIndicator_hasLaw μ t).map_eq

/-- The one-event probability of a threshold coordinate is the strict upper
tail of the original law. -/
theorem strictThresholdField_eval_oneProbability (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (t : ℝ) (z : Lattice) :
    (environmentLaw μ).real {ω | strictThresholdField t ω z = 1} =
      μ.real (Ioi t) := by
  have h := (hasLaw_strictThresholdField_eval μ t z).measureReal_eq
    (p := fun x : ℝ => x = 1) (measurableSet_singleton 1)
  simpa using h

/-- The finite strict-threshold count is the sum of the real
indicator field after applying `ENNReal.ofReal` term by term. -/
theorem animalThresholdCount_eq_sum_strictThresholdIndicator
    (U : Finset Lattice) (ω : Environment) (t : ℝ) :
    animalThresholdCount U ω t =
      ∑ z ∈ U, ENNReal.ofReal (strictThresholdIndicator t (ω z)) := by
  classical
  unfold animalThresholdCount
  apply Finset.sum_congr rfl
  intro z _
  by_cases h : t < ω z
  · simp [strictThresholdIndicator, mem_Iio, h]
  · simp [strictThresholdIndicator, mem_Iio, h]

/-- At nonnegative thresholds, taking the positive part does not change the
strict threshold indicator. -/
theorem strictThresholdIndicator_positivePart (t x : ℝ) (ht : 0 ≤ t) :
    strictThresholdIndicator t (max x 0) = strictThresholdIndicator t x := by
  have hmax : t < max x 0 ↔ t < x := by
    rw [lt_max_iff]
    constructor
    · rintro (h | h)
      · exact h
      · linarith
    · intro h
      exact Or.inl h
  simp [strictThresholdIndicator, hmax]

/-- At nonnegative thresholds, the strict-threshold count is unchanged by
replacing every weight with its positive part. -/
theorem animalThresholdCount_positivePart (U : Finset Lattice) (ω : Environment)
    (t : ℝ) (ht : 0 ≤ t) :
    animalThresholdCount U (fun z => max (ω z) 0) t = animalThresholdCount U ω t := by
  rw [animalThresholdCount_eq_sum_strictThresholdIndicator,
    animalThresholdCount_eq_sum_strictThresholdIndicator]
  apply Finset.sum_congr rfl
  intro z _
  exact congrArg ENNReal.ofReal (strictThresholdIndicator_positivePart t (ω z) ht)

end LPPDifferentiability
