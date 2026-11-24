/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.TopFlatSegment
public import Differentiability.Probability.FlatTopThinning
public import Differentiability.Probability.FlatEdgeDifferentiability
public import Differentiability.Model.OrientedPercolation
public import LPP_Foundations.Frozen.Analysis.ToQuadrant
public import LPP_Foundations.Frozen.Analysis.QuadrantExtension
public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import LPP_Foundations.Frozen.Model.LastPassage
import Mathlib.Tactic.Linarith

/-!
# The flat-segment theorem for weights at most one

This module assembles the three parts of the flat-segment theorem for a weight law with top
value `1`:

* (i) the description of the flat segment of the top shape, from
  `top_shape_flat_segment_of_expected_edge_rates`;
* (ii) the top shape equal to one forces the shape of the weights equal to one, from
  `gbar_eq_one_of_gtop_eq_one`;
* (iii) differentiability at the two ends of the flat segment, from
  `differentiableAt_flat_segment_endpoints_of_expected_edge_rate`. The hypothesis that the
  shape is one on `[1 - β, β]` comes from (i) and (ii).

## Main results

- `flat_segment_classification_of_weights_le_one`: the three parts (i), (ii) and (iii) together.

## References

- Georgiou, Rassoul-Agha and Seppäläinen (manuscript in preparation), the flat-edge theorem.
- C. Janjigian, F. Rassoul-Agha and T. Seppäläinen, *Differentiability of the shape function in
  the planar corner growth model*, Theorem `thm:flat-top`.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

namespace LPPDifferentiability

/-- **The flat-segment theorem for laws with weights at most one.** Let `ν` be a
weight law with top value `1`, an atom at `1` of mass strictly between `0` and `1`, and a
finite negative moment of order above one. Let `g` be the shape of the weights and `gtop` the
shape of the indicator of the sites of weight `1`. Let `R` be the set of expected half-line
edge rates `E a_{n+1} / (n+1)`.

* (i) If `R` is unbounded below, `gtop < 1` on the whole segment. If `β` is the greatest
  lower bound of `R`, then `1/2 ≤ β < 1` and `gtop = 1` exactly on `[1 - β, β]`.
* (ii) Wherever `gtop = 1` on the segment, also `g = 1`.
* (iii) If `β` is the greatest lower bound of `R`, the quadrant extension of `g` is
  differentiable at both ends `(β, 1 - β)` and `(1 - β, β)` of the flat segment.

This is the expected half-line edge-rate form of the flat-edge theorem of Georgiou,
Rassoul-Agha and Seppäläinen cited in Section `sec:flat` of the differentiability paper. -/
theorem flat_segment_classification_of_weights_le_one (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hle : ∀ᵐ t ∂ν, t ≤ 1) (hp₀ : 0 < ν {1}) (hp₁ : ν {1} < 1)
    (hneg : ∃ pneg : ℝ, 1 < pneg ∧
      (∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ pneg) ∂ν) < ∞)
    (g : Quadrant → ℝ) (hgcont : Continuous g)
    (hghom : ∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x)
    (hgconc : ∀ (x y : Quadrant) (r t : ℝ≥0), r + t = 1 →
      (r : ℝ) * g x + (t : ℝ) * g y ≤ g (r * x.1 + t * y.1, r * x.2 + t * y.2))
    (hgshape : ∀ᵐ ω ∂environmentLaw ν, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage ω 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ))
    (gtop : Quadrant → ℝ) (htcont : Continuous gtop)
    (hthom : ∀ (c : ℝ≥0) (x : Quadrant), gtop (c * x.1, c * x.2) = (c : ℝ) * gtop x)
    (htconc : ∀ (x y : Quadrant) (r t : ℝ≥0), r + t = 1 →
      (r : ℝ) * gtop x + (t : ℝ) * gtop y ≤ gtop (r * x.1 + t * y.1, r * x.2 + t * y.2))
    (htshape : ∀ᵐ ω ∂environmentLaw ν, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage (topField ω) 0 d - gtop ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ)) :
    let R : Set ℝ := Set.range fun n : ℕ =>
      (∫ ω, (halfLineEdge ω (n + 1) : ℝ) ∂environmentLaw ν) / ((n : ℝ) + 1)
    -- (i), infinite edge speed
    (¬ BddBelow R → ∀ t ∈ Icc (0 : ℝ) 1, gtop (toQuadrant (t, 1 - t)) < 1) ∧
    -- (i), finite edge speed
    (∀ β : ℝ, IsGLB R β → 1 / 2 ≤ β ∧ β < 1 ∧
      ∀ t ∈ Icc (0 : ℝ) 1, (gtop (toQuadrant (t, 1 - t)) = 1 ↔ t ∈ Icc (1 - β) β)) ∧
    -- (ii)
    (∀ t ∈ Icc (0 : ℝ) 1, gtop (toQuadrant (t, 1 - t)) = 1 →
      g (toQuadrant (t, 1 - t)) = 1) ∧
    -- (iii)
    (∀ β : ℝ, IsGLB R β →
      DifferentiableAt ℝ (quadrantExtension g) (β, 1 - β) ∧
        DifferentiableAt ℝ (quadrantExtension g) (1 - β, β)) := by
  intro R
  obtain ⟨hN9a, hN9b⟩ :=
    top_shape_flat_segment_of_expected_edge_rates ν hp₀ hp₁ gtop htcont hthom htconc htshape
  have hN10 : ∀ t ∈ Icc (0 : ℝ) 1, gtop (toQuadrant (t, 1 - t)) = 1 →
      g (toQuadrant (t, 1 - t)) = 1 := fun t ht h1 =>
    gbar_eq_one_of_gtop_eq_one ν hle hp₀ hp₁ hneg g hgcont hghom hgconc hgshape gtop htcont
      hthom htconc htshape t ht h1
  refine ⟨hN9a, hN9b, hN10, ?_⟩
  intro β hβ
  obtain ⟨hβhalf, hβone, hiff⟩ := hN9b β hβ
  refine differentiableAt_flat_segment_endpoints_of_expected_edge_rate ν hle hp₀ hp₁ hneg
    g hgcont hghom hgconc hgshape β hβhalf hβone hβ ?_
  intro t ht
  have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  exact hN10 t ht01 ((hiff t ht01).2 ht)

/-- Compatibility name for `flat_segment_classification_of_weights_le_one`. -/
alias flat_top_route_h := flat_segment_classification_of_weights_le_one

end LPPDifferentiability
