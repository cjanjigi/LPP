/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.UniformOriginMoments
public import ProbabilityBasics.Probability.UniformIncrementShift
public import ProbabilityBasics.Probability.TightMoment

/-!
# A stationary subsequential law of the random-origin increments

The first-moment bounds produce tightness and a weak subsequence, rather than
assuming either. The expected-rate limit in equation (2.1) of Liggett (1985)
remains an explicit intermediate input, to be supplied in the final application
to the array.
-/

public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace LPPDifferentiability

/-- The coordinate of the joint law has a finite first moment, inherited from its
increments with positive indices. -/
theorem integrable_uniformOriginIncrementLaw_eval {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hm : ∀ j, 0 < j → Measurable (X j))
    (hi : ∀ j, 0 < j → Integrable (X j) μ) (n k : ℕ) :
    Integrable (fun z : ℕ → ℝ => z k)
      (uniformOriginIncrementLaw μ X hm n : Measure (ℕ → ℝ)) := by
  rw [uniformOriginIncrementLaw_toMeasure]
  exact (integrable_map_measure (measurable_pi_apply k).aestronglyMeasurable
    (measurable_uniformOriginIncrement_sequence X hm n).aemeasurable).2
      (integrable_uniformOriginIncrement μ X hm hi n k)

/-- Coordinate expectation under the joint law is its expectation on the original
finite product. -/
theorem integral_uniformOriginIncrementLaw_eval {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hm : ∀ j, 0 < j → Measurable (X j)) (n k : ℕ) :
    (∫ z : ℕ → ℝ, z k ∂(uniformOriginIncrementLaw μ X hm n : Measure (ℕ → ℝ))) =
      ∫ p, uniformOriginIncrement X n k p ∂uniformOriginProduct μ n := by
  rw [uniformOriginIncrementLaw_toMeasure,
    integral_map (measurable_uniformOriginIncrement_sequence X hm n).aemeasurable
      (measurable_pi_apply k).aestronglyMeasurable]

/-- The joint law has exactly the same absolute coordinate moment as the finite
product; this is an equality of measures. -/
theorem integral_abs_uniformOriginIncrementLaw_eval {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hm : ∀ j, 0 < j → Measurable (X j)) (n k : ℕ) :
    (∫ z : ℕ → ℝ, |z k| ∂(uniformOriginIncrementLaw μ X hm n : Measure (ℕ → ℝ))) =
      ∫ p, |uniformOriginIncrement X n k p| ∂uniformOriginProduct μ n := by
  have htest : Measurable (fun z : ℕ → ℝ => |z k|) := by
    simpa only [Function.comp_def, Real.norm_eq_abs] using
      (measurable_norm.comp (measurable_pi_apply k) :
        Measurable (fun z : ℕ → ℝ => ‖z k‖))
  rw [uniformOriginIncrementLaw_toMeasure,
    integral_map (measurable_uniformOriginIncrement_sequence X hm n).aemeasurable
      htest.aestronglyMeasurable]

/-- The coordinate means of the law satisfy equation (2.12) of Liggett (1985). -/
theorem tendsto_integral_uniformOriginIncrementLaw_eval {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hm : ∀ j, 0 < j → Measurable (X j))
    (hi : ∀ j, 0 < j → Integrable (X j) μ) (γ : ℝ)
    (hγ : Tendsto (fun n : ℕ => (∫ ω, X (n + 1) ω ∂μ) / (n + 1 : ℝ)) atTop (𝓝 γ))
    (k : ℕ) :
    Tendsto (fun n => ∫ z : ℕ → ℝ, z k
      ∂(uniformOriginIncrementLaw μ X hm n : Measure (ℕ → ℝ))) atTop (𝓝 γ) := by
  simp_rw [integral_uniformOriginIncrementLaw_eval μ X hm]
  exact tendsto_integral_uniformOriginIncrement μ X hm hi γ hγ k

/-- The coordinate first moments admit one finite bound for each coordinate, with
every window size included. No tightness assumption is used. -/
theorem exists_uniformOriginIncrementLaw_coordinate_moment_bound {Ω A : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure A)
    (X Z : ℕ → Ω → ℝ) (g : A → ℝ)
    (hdom : ∀ j, 0 < j → ∀ᵐ ω ∂μ, X (j + 1) ω - X j ω ≤ Z j ω)
    (hlaw : ∀ j, 0 < j → IdentDistrib (Z j) g μ ν)
    (hg : Integrable g ν) (hm : ∀ j, 0 < j → Measurable (X j))
    (hi : ∀ j, 0 < j → Integrable (X j) μ) (γ : ℝ)
    (hγ : Tendsto (fun n : ℕ => (∫ ω, X (n + 1) ω ∂μ) / (n + 1 : ℝ)) atTop (𝓝 γ)) :
    ∃ C : ℕ → ℝ≥0∞, (∀ k, C k ≠ ∞) ∧ ∀ n k,
      (∫⁻ z : ℕ → ℝ, ENNReal.ofReal ‖z k‖
        ∂(uniformOriginIncrementLaw μ X hm n : Measure (ℕ → ℝ))) ≤ C k := by
  choose C hC using
    exists_integral_abs_uniformOriginIncrement_bound μ ν X Z g hdom hlaw hg hm hi γ hγ
  refine ⟨fun k => ENNReal.ofReal (C k), fun _ => ENNReal.ofReal_ne_top, fun n k => ?_⟩
  have heq := ofReal_integral_eq_lintegral_ofReal
    (integrable_uniformOriginIncrementLaw_eval μ X hm hi n k).norm
    (ae_of_all _ (fun z : ℕ → ℝ => norm_nonneg (z k)))
  rw [← heq]
  apply ENNReal.ofReal_le_ofReal
  simpa only [Real.norm_eq_abs, integral_abs_uniformOriginIncrementLaw_eval] using hC k n

/-- The first moments and the expected-rate conclusion produce one weak
subsequential probability law that is preserved by the sequence shift. -/
theorem exists_stationary_uniformOriginIncrementLaw_subsequence {Ω A : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure A)
    (X Z : ℕ → Ω → ℝ) (g : A → ℝ)
    (hdom : ∀ j, 0 < j → ∀ᵐ ω ∂μ, X (j + 1) ω - X j ω ≤ Z j ω)
    (hlaw : ∀ j, 0 < j → IdentDistrib (Z j) g μ ν)
    (hg : Integrable g ν) (hm : ∀ j, 0 < j → Measurable (X j))
    (hi : ∀ j, 0 < j → Integrable (X j) μ) (γ : ℝ)
    (hγ : Tendsto (fun n : ℕ => (∫ ω, X (n + 1) ω ∂μ) / (n + 1 : ℝ)) atTop (𝓝 γ)) :
    ∃ κ : ProbabilityMeasure (ℕ → ℝ), ∃ r : ℕ → ℕ,
      StrictMono r ∧
      Tendsto (fun i => uniformOriginIncrementLaw μ X hm (r i)) atTop (𝓝 κ) ∧
      MeasurePreserving sequenceShift (κ : Measure (ℕ → ℝ)) (κ : Measure (ℕ → ℝ)) := by
  obtain ⟨C, hfinite, hbound⟩ := exists_uniformOriginIncrementLaw_coordinate_moment_bound
    μ ν X Z g hdom hlaw hg hm hi γ hγ
  obtain ⟨κ, r, hr, hκ⟩ := exists_probabilityMeasure_tendsto_subseq_of_coordinate_moments
    (uniformOriginIncrementLaw μ X hm) C hfinite hbound
  exact ⟨κ, r, hr, hκ,
    measurePreserving_sequenceShift_of_tendsto_uniformOriginIncrementLaw μ X hm κ r hr hκ⟩

end LPPDifferentiability
