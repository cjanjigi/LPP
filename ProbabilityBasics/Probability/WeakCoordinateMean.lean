/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.WeakMean
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Coordinate means under weak convergence of sequence laws

Evaluation pushes the sequence laws forward to real laws. The identities below
supply the hypotheses of the scalar truncation and Fatou comparison in `WeakMean`.
They are used for the coordinate passage that follows equation (2.13) of Liggett
(1985). The coordinate moment, tail and mean estimates from earlier are inputs of
this file, to be supplied by the array construction.
-/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace LPPDifferentiability

/-- Weak convergence of sequence laws gives weak convergence of their coordinate
pushforwards. -/
theorem tendsto_coordinate_map
    (μ : ℕ → ProbabilityMeasure (ℕ → ℝ)) (ν : ProbabilityMeasure (ℕ → ℝ))
    (hweak : Tendsto μ atTop (𝓝 ν)) (k : ℕ) :
    Tendsto (fun n => (μ n).map (fun x => x k)) atTop
      (𝓝 (ν.map (fun x => x k))) :=
  ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous μ ν hweak (continuous_apply k)

/-- Scalar integrability under the coordinate law is exactly coordinate
integrability under the original law. -/
theorem integrable_id_coordinate_map_iff (ρ : ProbabilityMeasure (ℕ → ℝ)) (k : ℕ) :
    Integrable (fun t : ℝ => t) (ρ.map (fun x => x k) : Measure ℝ) ↔
      Integrable (fun x => x k) (ρ : Measure (ℕ → ℝ)) := by
  exact integrable_map_measure measurable_id.aestronglyMeasurable
    (measurable_pi_apply k).aemeasurable

/-- Ordinary coordinate means are unchanged by the pushforward. -/
theorem integral_coordinate_map (ρ : ProbabilityMeasure (ℕ → ℝ)) (k : ℕ) :
    (∫ t : ℝ, t ∂(ρ.map (fun x => x k) : Measure ℝ)) =
      ∫ x, x k ∂(ρ : Measure (ℕ → ℝ)) := by
  exact integral_map (measurable_pi_apply k).aemeasurable measurable_id.aestronglyMeasurable

/-- Absolute coordinate moments are unchanged by the pushforward. -/
theorem integral_abs_coordinate_map (ρ : ProbabilityMeasure (ℕ → ℝ)) (k : ℕ) :
    (∫ t : ℝ, |t| ∂(ρ.map (fun x => x k) : Measure ℝ)) =
      ∫ x, |x k| ∂(ρ : Measure (ℕ → ℝ)) := by
  exact integral_map (measurable_pi_apply k).aemeasurable
    continuous_abs.measurable.aestronglyMeasurable

/-- Strict positive-part tail integrals transfer exactly, including laws with
atoms at the threshold. -/
theorem integral_posPart_tail_coordinate_map
    (ρ : ProbabilityMeasure (ℕ → ℝ)) (k : ℕ) (R : ℝ) :
    (∫ t in {t : ℝ | R < max t 0}, max t 0
      ∂(ρ.map (fun x => x k) : Measure ℝ)) =
      ∫ x in {x : ℕ → ℝ | R < max (x k) 0}, max (x k) 0
        ∂(ρ : Measure (ℕ → ℝ)) := by
  exact setIntegral_map
    (measurableSet_lt measurable_const (measurable_id.max measurable_const))
    (continuous_id.max continuous_const).measurable.aestronglyMeasurable
    (measurable_pi_apply k).aemeasurable

/-- Bounded absolute coordinate moments yield integrability for the same weak
limit sequence law. -/
theorem integrable_coordinate_of_weak_abs_integral_le
    (μ : ℕ → ProbabilityMeasure (ℕ → ℝ)) (ν : ProbabilityMeasure (ℕ → ℝ))
    (hweak : Tendsto μ atTop (𝓝 ν)) (k : ℕ)
    (hμ : ∀ n, Integrable (fun x => x k) (μ n : Measure (ℕ → ℝ)))
    (C : ℝ) (hbound : ∀ n, (∫ x, |x k| ∂(μ n : Measure (ℕ → ℝ))) ≤ C) :
    Integrable (fun x => x k) (ν : Measure (ℕ → ℝ)) := by
  apply (integrable_id_coordinate_map_iff ν k).mp
  apply integrable_id_of_weak_abs_integral_le
    (fun n => (μ n).map (fun x => x k)) (ν.map (fun x => x k))
    (tendsto_coordinate_map μ ν hweak k)
    (fun n => (integrable_id_coordinate_map_iff (μ n) k).mpr (hμ n)) C
  intro n
  rw [integral_abs_coordinate_map]
  exact hbound n

/-- Positive coordinate tails and converging coordinate means give the lower bound
on the mean from Liggett (1985), under the same sequence limit law. These are
inputs from earlier estimates, not new premises of the final theorem. -/
theorem coordinate_mean_le_of_weak_abs_integral_le_pos_tails
    (μ : ℕ → ProbabilityMeasure (ℕ → ℝ)) (ν : ProbabilityMeasure (ℕ → ℝ))
    (hweak : Tendsto μ atTop (𝓝 ν)) (k : ℕ)
    (hμ : ∀ n, Integrable (fun x => x k) (μ n : Measure (ℕ → ℝ)))
    (C : ℝ) (hbound : ∀ n, (∫ x, |x k| ∂(μ n : Measure (ℕ → ℝ))) ≤ C)
    (htail : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ n,
      (∫ x in {x : ℕ → ℝ | R < max (x k) 0}, max (x k) 0
        ∂(μ n : Measure (ℕ → ℝ))) < ε)
    (γ : ℝ) (hmean : Tendsto (fun n => ∫ x, x k ∂(μ n : Measure (ℕ → ℝ)))
      atTop (𝓝 γ)) :
    γ ≤ ∫ x, x k ∂(ν : Measure (ℕ → ℝ)) := by
  rw [← integral_coordinate_map ν k]
  apply mean_le_of_weak_abs_integral_le_pos_tails
    (fun n => (μ n).map (fun x => x k)) (ν.map (fun x => x k))
    (tendsto_coordinate_map μ ν hweak k)
    (fun n => (integrable_id_coordinate_map_iff (μ n) k).mpr (hμ n)) C
  · intro n
    rw [integral_abs_coordinate_map]
    exact hbound n
  · intro ε hε
    obtain ⟨R, hR⟩ := htail ε hε
    refine ⟨R, fun n => ?_⟩
    rw [integral_posPart_tail_coordinate_map]
    exact hR n
  · simpa only [integral_coordinate_map] using hmean

end LPPDifferentiability
