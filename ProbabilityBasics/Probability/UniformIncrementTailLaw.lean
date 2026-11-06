/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.UniformIncrementLaw
public import ProbabilityBasics.Probability.UniformOriginTails
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Strict positive tails of the joint increment laws

Integration against the pushforward transfers the product-space estimates to the
same sequence laws used in the weak-limit construction of Liggett (1985).
-/

public section

open MeasureTheory ProbabilityTheory

namespace LPPDifferentiability

/-- Strict coordinate tail integrals under the joint law are exactly the
corresponding positive-tail integrals on the original finite product. -/
theorem integral_posPart_tail_uniformOriginIncrementLaw {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hm : ∀ j, 0 < j → Measurable (X j)) (n k : ℕ) (R : ℝ) :
    (∫ z in {z : ℕ → ℝ | R < max (z k) 0}, max (z k) 0
      ∂(uniformOriginIncrementLaw μ X hm n : Measure (ℕ → ℝ))) =
      ∫ p, positiveTail R (uniformOriginIncrement X n k p)
        ∂uniformOriginProduct μ n := by
  rw [← integral_indicator
    (measurableSet_lt measurable_const ((measurable_pi_apply k).max measurable_const))]
  change (∫ z : ℕ → ℝ, positiveTail R (z k)
    ∂(uniformOriginIncrementLaw μ X hm n : Measure (ℕ → ℝ))) = _
  rw [uniformOriginIncrementLaw_toMeasure]
  have htest : Measurable (fun z : ℕ → ℝ => positiveTail R (z k)) :=
    (measurable_positiveTail R).comp (measurable_pi_apply k)
  exact integral_map (measurable_uniformOriginIncrement_sequence X hm n).aemeasurable
    htest.aestronglyMeasurable

/-- A single strict threshold bounds the positive tails of every coordinate of
every finite-window law. The common-law inputs are explicit. -/
theorem uniformOriginIncrementLaw_positiveTail_uniform {Ω A : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure A)
    (X Z : ℕ → Ω → ℝ) (g : A → ℝ)
    (hdom : ∀ j, 0 < j → ∀ᵐ ω ∂μ, X (j + 1) ω - X j ω ≤ Z j ω)
    (hlaw : ∀ j, 0 < j → IdentDistrib (Z j) g μ ν)
    (hg : Integrable g ν) (hm : ∀ j, 0 < j → Measurable (X j))
    (hi : ∀ j, 0 < j → Integrable (X j) μ) :
    ∀ ε > 0, ∃ R : ℝ, 0 ≤ R ∧ ∀ S ≥ R, ∀ n k,
      (∫ z in {z : ℕ → ℝ | S < max (z k) 0}, max (z k) 0
        ∂(uniformOriginIncrementLaw μ X hm n : Measure (ℕ → ℝ))) < ε := by
  intro ε hε
  obtain ⟨R, hR, htail⟩ := uniformOriginIncrement_positiveTail_uniform
    μ ν X Z g hdom hlaw hg hm hi ε hε
  refine ⟨R, hR, fun S hS n k => ?_⟩
  rw [integral_posPart_tail_uniformOriginIncrementLaw]
  exact htail S hS n k

end LPPDifferentiability
