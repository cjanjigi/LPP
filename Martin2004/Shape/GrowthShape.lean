/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.ShapeAboveMean
public import ProbabilityBasics.Probability.SqrtTailMoments

/-!
# Shared steps for the growth-shape theorems (Martin, Theorem 5.1)

Martin (2004), Section 5.3, first paragraph. For the last-passage part (i) of Theorem 5.1 the
positive mean gives `g x ≥ ‖x‖ E X`, which is the lower bound on the shape that the growth-set
argument needs. The lemma `level_mul_integral_le_shape_of_negative_moment_and_positive_tail` proves
this bound, but it states its negative-moment hypothesis as "some moment of order `p > 1` is
finite" and its closeness hypothesis with a threshold `N ≥ 1`. The statement
`martin_last_passage_growth_shape` in `Frozen/Martin/GrowthShape.lean` states the negative
hypothesis as the integrated square-root tail and the closeness without the bound `N ≥ 1`. The two
adapters below carry the forms in `Frozen/` to the forms of that lemma, so that the proof of the
statement can use it.

## Main results

- `exists_one_lt_negative_moment_of_sqrt_tails`: the square-root tails give a finite moment of
  order `2`.
- `shape_lower_bound_of_positive_mean`: a positive mean bounds the shape from below by a multiple
  of `‖x‖`.

## References

- J. B. Martin, *Limiting shape for directed percolation models*, Ann. Probab. 32 (2004),
  Theorem 5.1 and Section 5.3.
-/

public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace LPPDifferentiability

/-- The integrated square-root tails (5.1) and (5.2) with `d = 2` give a finite negative moment of
order `2`, which is a moment of order `p > 1`. This is the adapter from the form of the hypothesis
`hneg` in `Frozen/` to the form used by `ShapeAboveMean`. The second moment of the weight is finite
by `sqrt_tail_integrable_sq` (see the proof of Martin (2004), Lemma 4.3), and the negative part
squared is at most the square. -/
theorem exists_one_lt_negative_moment_of_sqrt_tails (μ : Measure ℝ)
    (hneg : (∫⁻ t in Iio (0 : ℝ), (μ (Iic t)) ^ (1 / 2 : ℝ)) < ∞)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞) :
    ∃ p : ℝ, 1 < p ∧ (∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ p) ∂μ) < ∞ := by
  refine ⟨2, one_lt_two, ?_⟩
  -- the second moment is finite
  have hsq : (∫⁻ t, ENNReal.ofReal (t ^ 2) ∂μ) < ∞ :=
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun t => sq_nonneg t)).1
      (sqrt_tail_integrable_sq μ hneg hpos).hasFiniteIntegral
  -- the negative part to the power `2` is at most `t ^ 2`
  have hle : ∀ t : ℝ, ENNReal.ofReal ((max (-t) 0) ^ (2 : ℝ)) ≤ ENNReal.ofReal (t ^ 2) := by
    intro t
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Real.rpow_two]
    have habs : max (-t) 0 ≤ |t| := max_le (neg_le_abs t) (abs_nonneg t)
    calc (max (-t) 0) ^ 2 ≤ |t| ^ 2 := pow_le_pow_left₀ (le_max_right _ _) habs 2
      _ = t ^ 2 := sq_abs t
  exact lt_of_le_of_lt (lintegral_mono hle) hsq

/-- The lower bound on the last-passage shape from a positive mean weight (Martin (2004),
Section 5.3: `g x ≥ ‖x‖ E X`). Under (5.1), (5.2) and `E X > 0`, any shape function `g` that is
continuous, homogeneous, concave and almost surely close to the last-passage times satisfies
`c (x.1 + x.2) ≤ g x` at every point of the quadrant, with `c = E X > 0`. The closeness is stated as
in `Frozen/Martin/GrowthShape.lean`, without the bound `1 ≤ N` that `ShapeAboveMean` asks for; the
threshold is replaced by `max N 1`. -/
theorem shape_lower_bound_of_positive_mean (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : (∫⁻ t in Iio (0 : ℝ), (μ (Iic t)) ^ (1 / 2 : ℝ)) < ∞)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞)
    (hmean : 0 < ∫ t : ℝ, t ∂μ)
    (g : Quadrant → ℝ) (hgc : Continuous g)
    (hgh : ∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x)
    (hgconc : ∀ (x y : Quadrant) (a b : ℝ≥0), a + b = 1 →
      (a : ℝ) * g x + (b : ℝ) * g y ≤
        g (a * x.1 + b * y.1, a * x.2 + b * y.2))
    (hgae : ∀ᵐ ω ∂environmentLaw μ, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ z : ℕ × ℕ,
      N ≤ z.1 + z.2 →
        |lastPassage ω (0, 0) z - g ((z.1 : ℝ≥0), (z.2 : ℝ≥0))| ≤
          ε * ((z.1 + z.2 : ℕ) : ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : Quadrant, c * ((x.1 : ℝ) + x.2) ≤ g x := by
  -- the closeness with a threshold of at least `1`
  have hgae' : ∀ᵐ ω ∂environmentLaw μ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage ω 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ) := by
    filter_upwards [hgae] with ω hω ε hε
    obtain ⟨N, hN⟩ := hω ε hε
    exact ⟨max N 1, le_max_right N 1, fun d hd => hN d (le_trans (le_max_left N 1) hd)⟩
  refine ⟨∫ t : ℝ, t ∂μ, hmean, fun x => ?_⟩
  have h := level_mul_integral_le_shape_of_negative_moment_and_positive_tail μ
    (exists_one_lt_negative_moment_of_sqrt_tails μ hneg hpos) hpos g hgc hgh hgconc hgae' x
  rwa [mul_comm] at h

end LPPDifferentiability
