/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Frozen.Martin.Shape
public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import LPP_Foundations.Frozen.Model.LastPassage
public import LPP_Foundations.Frozen.Model.Quadrant
public import ProbabilityBasics.Probability.SqrtTailMoments
public import Martin2004.Shape.BoundaryAsymptotics
public import Martin2004.Shape.MartinShapeExpectedRate
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Behaviour of the shape function at the boundary of the quadrant

The theorem here is the proof of the statement `martin_boundary_asymptotics` in
`Frozen/Martin/BoundaryAsymptotics.lean` (Martin (2004), Theorem 2.4). Under the two integrated
square-root tail conditions, the weight has a finite second moment, the shape function `g` exists
and is unique, and `g (1, α) = m + 2 s √α + o(√α)` as `α` decreases to `0`, where `m` is the mean
and `s` the standard deviation of the weight.

## Main results

- `martin_boundary_asymptotics`: existence and uniqueness of the shape function together with its
  expansion at the boundary.

## References

- J. B. Martin, *Limiting shape for directed percolation models*, Ann. Probab. 32 (2004),
  Theorem 2.4.
-/

@[expose] public section

open MeasureTheory Filter Set Asymptotics
open scoped NNReal ENNReal Topology

namespace LPPDifferentiability.Full

/-- Martin (2004), Theorem 2.4: under the two integrated square-root tail conditions (2.6) and
(2.7), the weight has a finite second moment, and the unique shape function `g` of
`exists_unique_shape_martin` satisfies `g (1, a) = m + 2 s √a + o(√a)` as `a` decreases to `0`,
where `m` is the mean and `s` the standard deviation of the weight. -/
theorem martin_boundary_asymptotics
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : (∫⁻ t in Iio (0 : ℝ), (μ (Iic t)) ^ (1 / 2 : ℝ)) < ∞)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞) :
    Integrable (fun t : ℝ => t ^ 2) μ ∧
    ∃! g : Quadrant → ℝ,
      Continuous g ∧
      (∀ (c : ℝ≥0) (x : Quadrant),
        g (c * x.1, c * x.2) = (c : ℝ) * g x) ∧
      (∀ (x y : Quadrant) (a b : ℝ≥0), a + b = 1 →
        (a : ℝ) * g x + (b : ℝ) * g y ≤
          g (a * x.1 + b * y.1, a * x.2 + b * y.2)) ∧
      (∀ᵐ ω ∂environmentLaw μ,
        ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ z : ℕ × ℕ,
          N ≤ z.1 + z.2 →
          |lastPassage ω (0, 0) z - g ((z.1 : ℝ≥0), (z.2 : ℝ≥0))| ≤
            ε * ((z.1 + z.2 : ℕ) : ℝ)) ∧
      (fun α : ℝ≥0 => g (1, α) - ((∫ t : ℝ, t ∂μ) +
          2 * Real.sqrt (∫ t : ℝ, (t - ∫ s : ℝ, s ∂μ) ^ 2 ∂μ) * Real.sqrt (α : ℝ)))
        =o[𝓝[>] (0 : ℝ≥0)] (fun α : ℝ≥0 => Real.sqrt (α : ℝ)) := by
  -- As in the proof of Martin (2004), Lemma 4.3: the square-root tails give a finite second
  -- moment.
  have hint : Integrable (fun t : ℝ => t ^ 2) μ := sqrt_tail_integrable_sq μ hneg hpos
  refine ⟨hint, ?_⟩
  -- the shape function and its four clauses, from `exists_unique_shape_martin`
  obtain ⟨g, hg, huniq⟩ := exists_unique_shape_martin μ hneg hpos
  -- the shape function is the limit of the expected rates
  have hshape : IsExpectedRateShape μ g :=
    LPPDifferentiability.Martin.martin_shape_tendsto_expected_rate μ hneg hpos g hg
  -- Theorem 2.4 (2.8), by Lemma 4.6 for the law and for Exp(1), with the extra clause
  have hasymp := martin_shape_boundary_asymptotics μ hneg hpos g hshape
  refine ⟨g, ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2, hasymp⟩, ?_⟩
  -- uniqueness already follows from the first four clauses
  intro g' hg'
  exact huniq g' ⟨hg'.1, hg'.2.1, hg'.2.2.1, hg'.2.2.2.1⟩

end LPPDifferentiability.Full
