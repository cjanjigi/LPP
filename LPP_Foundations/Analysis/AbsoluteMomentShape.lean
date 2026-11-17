/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.Quadrant
public import ProbabilityBasics.Probability.AbsoluteMomentTail
public import Martin2004.Shape.ExpectedRateShape
public import Martin2004.Shape.BoundaryAsymptotics
import ProbabilityBasics.Probability.AbsoluteMomentLowerTail
import ProbabilityBasics.Probability.SqrtTailMoments
import Martin2004.Frozen.Martin.Shape
import Martin2004.Shape.MartinShapeExpectedRate

/-!
# Shape consequences of an absolute moment

A finite absolute moment above order two supplies the square-root tail
conditions used by Martin's shape and boundary theorems. These results apply
those theorems to a supplied expected-rate shape.
-/

@[expose] public section

open MeasureTheory Asymptotics
open scoped NNReal ENNReal Topology

namespace LPPDifferentiability

/-- A finite absolute moment of some order greater than two, as in Janjigian
and Rassoul-Agha, arXiv:1810.03580v3, assumption (2.1), makes every canonical
expected-rate shape continuous, homogeneous, and concave as in Martin (2004),
Section 5.3. -/
theorem expected_rate_shape_geometry_of_absolute_moment
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (g : Quadrant → ℝ)
    (habs : ∃ p : ℝ, 2 < p ∧
      (∫⁻ x, ENNReal.ofReal (|x| ^ p) ∂μ) < ∞)
    (hg : IsExpectedRateShape μ g) :
    Continuous g ∧
      (∀ (c : ℝ≥0) (x : Quadrant),
        g (c * x.1, c * x.2) = (c : ℝ) * g x) ∧
      (∀ (x y : Quadrant) (a b : ℝ≥0), a + b = 1 →
        (a : ℝ) * g x + (b : ℝ) * g y ≤
          g (a * x.1 + b * y.1, a * x.2 + b * y.2)) := by
  obtain ⟨p, hp, hmoment⟩ := habs
  -- Assumption (2.1) supplies Martin's positive square-root tail.
  have hpositive :=
    ProbabilityBasics.negative_moment_and_positive_tail_of_absolute_moment
      μ hp hmoment
  have hpos : (∫⁻ t in Set.Ioi (0 : ℝ), (μ (Set.Ioi t)) ^ (1 / 2 : ℝ)) < ∞ :=
    hpositive.2
  -- The closed lower-tail adapter supplies Martin's condition (2.7).
  have hneg :=
    ProbabilityBasics.integrated_sqrt_lower_tail_lt_top_of_absolute_moment
      μ hp hmoment
  -- Martin's Section 5.3 theorem provides the shape and its four clauses.
  obtain ⟨g₀, hg₀, -⟩ := exists_unique_shape_martin μ hneg hpos
  -- The shape clauses make this witness the canonical expected-rate shape.
  have hrate₀ : IsExpectedRateShape μ g₀ :=
    Martin.martin_shape_tendsto_expected_rate μ hneg hpos g₀ hg₀
  -- Uniqueness of expected-rate limits identifies the supplied shape.
  have hEq : g = g₀ := isExpectedRateShape_unique μ hg hrate₀
  rw [hEq]
  exact ⟨hg₀.1, hg₀.2.1, hg₀.2.2.1⟩

/-- A finite absolute moment above order two gives the finite second moment
and Martin's boundary expansion for a supplied expected-rate shape. The
expansion is Martin (2004), Theorem 2.4; the moment input is assumption (2.1)
of Janjigian and Rassoul-Agha, arXiv:1810.03580v3. -/
theorem expected_rate_shape_boundary_asymptotics_and_second_moment_of_absolute_moment
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (g : Quadrant → ℝ)
    (habs : ∃ p : ℝ, 2 < p ∧
      (∫⁻ x, ENNReal.ofReal (|x| ^ p) ∂μ) < ∞)
    (hg : IsExpectedRateShape μ g) :
    Integrable (fun t : ℝ => t ^ 2) μ ∧
      (fun α : ℝ≥0 => g (1, α) - ((∫ t : ℝ, t ∂μ) +
        2 * Real.sqrt (∫ t : ℝ, (t - ∫ s : ℝ, s ∂μ) ^ 2 ∂μ) *
          Real.sqrt (α : ℝ))) =o[𝓝[>] (0 : ℝ≥0)]
        (fun α : ℝ≥0 => Real.sqrt (α : ℝ)) := by
  obtain ⟨p, hp, hmoment⟩ := habs
  -- The same adapters give both integrated square-root tail conditions.
  have hpositive :=
    ProbabilityBasics.negative_moment_and_positive_tail_of_absolute_moment
      μ hp hmoment
  have hpos : (∫⁻ t in Set.Ioi (0 : ℝ), (μ (Set.Ioi t)) ^ (1 / 2 : ℝ)) < ∞ :=
    hpositive.2
  have hneg :=
    ProbabilityBasics.integrated_sqrt_lower_tail_lt_top_of_absolute_moment
      μ hp hmoment
  -- Martin's Lemma 4.3 gives the second moment from these tails.
  have hsecondMoment := sqrt_tail_integrable_sq μ hneg hpos
  -- Theorem 2.4 gives the boundary expansion directly for this shape.
  have hboundary := martin_shape_boundary_asymptotics μ hneg hpos g hg
  exact ⟨hsecondMoment, hboundary⟩

end LPPDifferentiability
