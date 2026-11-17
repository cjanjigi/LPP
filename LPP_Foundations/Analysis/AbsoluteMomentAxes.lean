/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Shape.ExpectedRateShape

import ProbabilityBasics.Probability.AbsoluteMomentTail
import Martin2004.Probability.WeakNegativeShape

/-!
# Axes and symmetry from an absolute moment

A finite absolute moment above order two supplies the one-sided tail hypotheses
for the weak shape theorem. That theorem's unique expected-rate shape already
has both mean-valued axes and coordinate-swap symmetry.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LPPDifferentiability

/-- A native absolute moment above order two forces the canonical expected-rate
shape to be symmetric and to equal the mean times length on both axes. This
extracts the geometry in Martin's weak shape theorem; see GRS
arXiv:1510.00860v2, (2.6)–(2.8). -/
theorem expected_rate_shape_axes_and_symmetry_of_absolute_moment
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ x, ENNReal.ofReal (|x| ^ p) ∂μ) < ∞)
    (g : Quadrant → ℝ) (hg : IsExpectedRateShape μ g) :
    (∀ x : Quadrant, g x.swap = g x) ∧
    (∀ s : ℝ≥0, g (s, 0) = (∫ t : ℝ, t ∂μ) * (s : ℝ)) ∧
    (∀ s : ℝ≥0, g (0, s) = (∫ t : ℝ, t ∂μ) * (s : ℝ)) := by
  obtain ⟨p, hp, hpMoment⟩ := hmoment

  -- The native absolute moment gives the two tail bounds of the weak theorem.
  have htails :=
    ProbabilityBasics.negative_moment_and_positive_tail_of_absolute_moment
      μ hp hpMoment
  have hnegative := htails.1
  have hpositive := htails.2

  -- The negative moment and positive tail give the actual first moment.
  have hintegrable : Integrable (fun t : ℝ => t) μ :=
    integrable_id_of_negative_moment_and_positive_tail μ hnegative hpositive

  -- The unique weak expected rate contains both axes and swap symmetry.
  obtain ⟨g₀, hg₀, _hunique⟩ :=
    exists_unique_continuous_lastPassage_real_expected_rate_of_integrable_and_positive_tail
      μ hintegrable hpositive
  have hrate₀ : IsExpectedRateShape μ g₀ := hg₀.1.1.1

  -- Uniqueness identifies the supplied canonical expected rate with that witness.
  have hsame : g = g₀ := isExpectedRateShape_unique μ hg hrate₀
  have hsymmetry₀ : ∀ x : Quadrant, g₀ x.swap = g₀ x := hg₀.1.2.2.2.1
  have hhorizontal₀ : ∀ s : ℝ≥0,
      g₀ (s, 0) = (∫ t : ℝ, t ∂μ) * (s : ℝ) := hg₀.1.1.2.2.2.1
  have hvertical₀ : ∀ s : ℝ≥0,
      g₀ (0, s) = (∫ t : ℝ, t ∂μ) * (s : ℝ) := hg₀.1.1.2.2.2.2.1

  refine ⟨?_, ?_, ?_⟩
  · intro x
    rw [hsame]
    exact hsymmetry₀ x
  · intro s
    rw [hsame]
    exact hhorizontal₀ s
  · intro s
    rw [hsame]
    exact hvertical₀ s

end LPPDifferentiability
