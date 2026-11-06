/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Frozen.Martin.Shape
public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import LPP_Foundations.Frozen.Model.FirstPassage
public import LPP_Foundations.Frozen.Model.LastPassage
public import LPP_Foundations.Frozen.Model.Quadrant
public import Martin2004.Probability.NegatedLaw
public import ProbabilityBasics.Probability.SqrtTailMoments
public import Martin2004.Shape.BoundaryAsymptotics
public import Martin2004.Shape.FirstPassageBoundaryAsymptotics
public import Martin2004.Shape.FirstPassageShape
public import Martin2004.Shape.MartinShapeExpectedRate
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Boundary behaviour of the first-passage shape function

The theorem here is the proof of the statement `martin_first_passage_boundary_asymptotics` in
`Frozen/Martin/FirstPassageBoundaryAsymptotics.lean` (Martin (2004), Corollary 2.5(ii)). The
first-passage shape function is minus the last-passage shape function of the negated weight law,
so the expansion follows from the last-passage expansion (Theorem 2.4) applied to that law.

## Main results

- `martin_first_passage_boundary_asymptotics`: existence and uniqueness of the first-passage shape
  function together with its expansion `h (1, α) = m - 2 s √α + o(√α)` at the boundary.

## References

- J. B. Martin, *Limiting shape for directed percolation models*, Ann. Probab. 32 (2004),
  Corollary 2.5(ii) and Theorem 2.4.
-/

@[expose] public section

open MeasureTheory Filter Set Asymptotics
open scoped NNReal ENNReal Topology

namespace LPPDifferentiability.Full

/-- Martin (2004), Corollary 2.5(ii): under (2.6) and (2.7) the weight has a finite second moment,
and there is exactly one continuous, homogeneous, convex function `h` on the closed quadrant that
approximates the first-passage time `S(z)` uniformly within `ε ‖z‖` for all long `z`, almost
surely; it satisfies `h (1, a) = m - 2 s √a + o(√a)` as `a` decreases to `0`. The paper gives no
proof beyond the sign change described after Theorem 2.4: `h` is minus the shape `g` of the
negated law, and Theorem 2.4 applied to that law gives the expansion. -/
theorem martin_first_passage_boundary_asymptotics
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : (∫⁻ t in Iio (0 : ℝ), (μ (Iic t)) ^ (1 / 2 : ℝ)) < ∞)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞) :
    Integrable (fun t : ℝ => t ^ 2) μ ∧
    ∃! h : Quadrant → ℝ,
      Continuous h ∧
      (∀ (c : ℝ≥0) (x : Quadrant),
        h (c * x.1, c * x.2) = (c : ℝ) * h x) ∧
      (∀ (x y : Quadrant) (a b : ℝ≥0), a + b = 1 →
        h (a * x.1 + b * y.1, a * x.2 + b * y.2) ≤
          (a : ℝ) * h x + (b : ℝ) * h y) ∧
      (∀ᵐ ω ∂environmentLaw μ,
        ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ z : ℕ × ℕ,
          N ≤ z.1 + z.2 →
          |firstPassage ω (0, 0) z - h ((z.1 : ℝ≥0), (z.2 : ℝ≥0))| ≤
            ε * ((z.1 + z.2 : ℕ) : ℝ)) ∧
      (fun α : ℝ≥0 => h (1, α) - ((∫ t : ℝ, t ∂μ) -
          2 * Real.sqrt (∫ t : ℝ, (t - ∫ s : ℝ, s ∂μ) ^ 2 ∂μ) * Real.sqrt (α : ℝ)))
        =o[𝓝[>] (0 : ℝ≥0)] (fun α : ℝ≥0 => Real.sqrt (α : ℝ)) := by
  -- As in the proof of Martin (2004), Lemma 4.3: the square-root tails give a finite second
  -- moment.
  have hint : Integrable (fun t : ℝ => t ^ 2) μ := sqrt_tail_integrable_sq μ hneg hpos
  refine ⟨hint, ?_⟩
  -- The sign change described after Martin (2004), Theorem 2.4: the negated law has the two
  -- tails exchanged.
  have hnegν : (∫⁻ t in Iio (0 : ℝ), ((μ.map Neg.neg) (Iic t)) ^ (1 / 2 : ℝ)) < ∞ :=
    (negated_lower_sqrt_tail_iff μ).2 hpos
  have hposν : (∫⁻ t in Ioi (0 : ℝ), ((μ.map Neg.neg) (Ioi t)) ^ (1 / 2 : ℝ)) < ∞ :=
    (negated_upper_sqrt_tail_iff μ).2 hneg
  -- The shape `g` of the negated law, and the first-passage shape `h` of `μ`.
  obtain ⟨g, hg, -⟩ := exists_unique_shape_martin (μ.map Neg.neg) hnegν hposν
  obtain ⟨h, hh, huniq⟩ := exists_unique_firstPassage_shape_martin μ hneg hpos
  -- The sign change: `-g` has the clauses of the first-passage shape, so `-g = h`.
  have hhg : (fun x : Quadrant => -g x) = h :=
    huniq _ (firstPassage_shape_clauses_of_negated_shape μ g hg)
  have hh1 : ∀ α : ℝ≥0, h (1, α) = -g (1, α) := fun α => (congrFun hhg (1, α)).symm
  -- Theorem 2.4 (2.8) for the negated law, whose shape is the limit of the expected rates.
  have hshape : IsExpectedRateShape (μ.map Neg.neg) g :=
    LPPDifferentiability.Martin.martin_shape_tendsto_expected_rate (μ.map Neg.neg) hnegν hposν g hg
  have hasymp := martin_shape_boundary_asymptotics (μ.map Neg.neg) hnegν hposν g hshape
  -- The negated law has mean `-m` and the same variance.
  rw [negated_variance, negated_mean] at hasymp
  refine ⟨h, ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2, ?_⟩, fun f hf => huniq f ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1⟩⟩
  -- Negate the expansion of `g`.
  refine hasymp.neg_left.congr_left fun α => ?_
  rw [hh1 α]
  ring

end LPPDifferentiability.Full
