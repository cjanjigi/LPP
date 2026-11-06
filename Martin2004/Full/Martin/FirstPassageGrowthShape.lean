/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Shape.FirstPassageShape
public import Martin2004.Analysis.GrowthSetInclusion
public import LPP_Foundations.Frozen.Model.LastPassage
public import LPP_Foundations.Frozen.Model.Quadrant
public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import LPP_Foundations.Frozen.Model.FirstPassage
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The first-passage growth shape theorem

The theorem here is the proof of the statement `martin_first_passage_growth_shape` in
`Frozen/Martin/FirstPassageGrowthShape.lean` (Martin (2004), Theorem 5.1(ii) for `d = 2`). The
first-passage shape function `h` is the uniform limit of the first-passage times, and when `h`
grows at least linearly, the set of points reached by time `t`, scaled by `1/t`, lies between
`(1 - ε) C` and `(1 + ε) C` for all large `t`, almost surely, where `C = {x : h x ≤ 1}`.

## Main results

- `martin_first_passage_growth_shape`: existence and uniqueness of `h`, together with the
  growth-set inclusions.

## References

- J. B. Martin, *Limiting shape for directed percolation models*, Ann. Probab. 32 (2004),
  Theorem 5.1(ii) and Section 5.3.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal Pointwise

namespace LPPDifferentiability.Full

/-- Martin (2004), Theorem 5.1(ii), `d = 2`, in growth-set form: under (5.1) and (5.2) with
`d = 2`, let `h` be the unique first-passage shape function. If `h x ≥ c ‖x‖` for some `c > 0`
(the paper's condition `inf h(x)/‖x‖ > 0`), then almost surely, for every `ε > 0` and all large
`t`, `(1 - ε) C` is inside `C(t)/t`, which is inside `(1 + ε) C`, where
`C(t) = {x : S(⌊x⌋) ≤ t}` and `C = {x : h x ≤ 1}`. -/
theorem martin_first_passage_growth_shape
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : (∫⁻ t in Iio (0 : ℝ), (μ (Iic t)) ^ (1 / 2 : ℝ)) < ∞)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞) :
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
      ((∃ c : ℝ, 0 < c ∧ ∀ x : Quadrant, c * ((x.1 : ℝ) + x.2) ≤ h x) →
        ∀ᵐ ω ∂environmentLaw μ, ∀ ε : ℝ≥0, 0 < ε → ∃ t₀ : ℝ≥0, ∀ t : ℝ≥0, t₀ ≤ t →
          (1 - ε) • {x : Quadrant | h x ≤ 1} ⊆
              t⁻¹ • {x : Quadrant | firstPassage ω 0 (⌊x.1⌋₊, ⌊x.2⌋₊) ≤ (t : ℝ)} ∧
            t⁻¹ • {x : Quadrant | firstPassage ω 0 (⌊x.1⌋₊, ⌊x.2⌋₊) ≤ (t : ℝ)} ⊆
              (1 + ε) • {x : Quadrant | h x ≤ 1}) :=
by
  -- Section 5.3: the first four conjuncts are the uniform first-passage shape theorem, the
  -- sign change of the uniform last-passage shape (see the remark after Theorem 2.4).
  obtain ⟨h, ⟨hcont, hhom, hconv, hclose⟩, huniq⟩ :=
    exists_unique_firstPassage_shape_martin μ hneg hpos
  -- Section 5.3: under the lower bound on `h` (the hypothesis of part (ii)), almost sure
  -- closeness on all long points gives the growth-set inclusions, environment by environment.
  refine ⟨h, ⟨hcont, hhom, hconv, hclose, fun hlow => ?_⟩,
    fun y hy => huniq y ⟨hy.1, hy.2.1, hy.2.2.1, hy.2.2.2.1⟩⟩
  filter_upwards [hclose] with ω hω
  exact firstPassage_growth_set_inclusions ω h hcont hhom hlow hω

end LPPDifferentiability.Full
