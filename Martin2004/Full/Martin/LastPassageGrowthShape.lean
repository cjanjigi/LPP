/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Frozen.Martin.Shape
public import Martin2004.Analysis.GrowthSetInclusion
public import Martin2004.Shape.GrowthShape
public import LPP_Foundations.Frozen.Model.LastPassage
public import LPP_Foundations.Frozen.Model.Quadrant
public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The last-passage growth shape theorem

The theorem here is the proof of the statement `martin_last_passage_growth_shape` in
`Frozen/Martin/GrowthShape.lean` (Martin (2004), Theorem 5.1(i) for `d = 2`). With a positive
mean weight, the set of points reached by last-passage time `t`, scaled by `1/t`, lies between
`(1 - ε) B` and `(1 + ε) B` for all large `t`, almost surely, where `B = {x : g x ≤ 1}` and `g`
is the shape function.

## Main results

- `martin_last_passage_growth_shape`: existence and uniqueness of `g`, together with the
  growth-set inclusions.

## References

- J. B. Martin, *Limiting shape for directed percolation models*, Ann. Probab. 32 (2004),
  Theorem 5.1(i) and Section 5.3.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal Pointwise

namespace LPPDifferentiability.Full

/-- Martin (2004), Theorem 5.1(i), `d = 2`, in growth-set form: under (5.1) and (5.2) with
`d = 2`, and a positive mean weight, let `g` be the unique shape function. Almost surely, for
every `ε > 0` and all large times `t`, the scaled limit set `(1 - ε) B` is inside `B(t)/t`, which
is inside `(1 + ε) B`. Here `B(t) = {x : T(⌊x⌋) ≤ t}` is the last-passage growth set at time `t`
and `B = {x : g x ≤ 1}`. Scalars are nonnegative reals, so `1 - ε` is truncated at `0`. -/
theorem martin_last_passage_growth_shape
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : (∫⁻ t in Iio (0 : ℝ), (μ (Iic t)) ^ (1 / 2 : ℝ)) < ∞)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞)
    (hmean : 0 < ∫ t : ℝ, t ∂μ) :
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
      (∀ᵐ ω ∂environmentLaw μ, ∀ ε : ℝ≥0, 0 < ε → ∃ t₀ : ℝ≥0, ∀ t : ℝ≥0, t₀ ≤ t →
        (1 - ε) • {x : Quadrant | g x ≤ 1} ⊆
            t⁻¹ • {x : Quadrant | lastPassage ω 0 (⌊x.1⌋₊, ⌊x.2⌋₊) ≤ (t : ℝ)} ∧
          t⁻¹ • {x : Quadrant | lastPassage ω 0 (⌊x.1⌋₊, ⌊x.2⌋₊) ≤ (t : ℝ)} ⊆
            (1 + ε) • {x : Quadrant | g x ≤ 1}) :=
by
  -- Section 5.3: the first four conjuncts are the uniform shape theorem, which holds under
  -- (5.1) and (5.2) alone (Lemmas 5.2 to 5.5 together with Theorem 2.3).
  obtain ⟨g, ⟨hcont, hhom, hconc, hclose⟩, huniq⟩ := exists_unique_shape_martin μ hneg hpos
  -- Section 5.3, first paragraph: the positive mean bounds `g x` below by `‖x‖ E X`.
  have hlow : ∃ c : ℝ, 0 < c ∧ ∀ x : Quadrant, c * ((x.1 : ℝ) + x.2) ≤ g x :=
    shape_lower_bound_of_positive_mean μ hneg hpos hmean g hcont hhom hconc hclose
  -- Section 5.3: almost sure closeness on all long points gives the growth-set inclusions,
  -- environment by environment.
  refine ⟨g, ⟨hcont, hhom, hconc, hclose, ?_⟩,
    fun y hy => huniq y ⟨hy.1, hy.2.1, hy.2.2.1, hy.2.2.2.1⟩⟩
  filter_upwards [hclose] with ω hω
  exact lastPassage_growth_set_inclusions ω g hcont hhom hlow hω

end LPPDifferentiability.Full
