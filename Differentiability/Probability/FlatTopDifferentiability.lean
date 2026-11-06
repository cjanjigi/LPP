/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.FlatTopRouteH
public import Differentiability.Probability.FlatShiftAdapters
public import Differentiability.Analysis.FlatConeDifferentiability
public import Differentiability.Model.OrientedPercolation
public import LPP_Foundations.Frozen.Analysis.ToQuadrant
public import LPP_Foundations.Frozen.Analysis.QuadrantExtension
public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import LPP_Foundations.Frozen.Model.LastPassage
import Mathlib.Tactic.Linarith

/-!
# Differentiability on the flat segment for a general weight law

If the expected top-indicator passage times, divided by their length, tend to `1` in the
direction `(a, 1 - a)`, then the shape of a general weight law is differentiable there.

The proof shifts the law so that the top of the support becomes `1`, applies the flat-segment
theorem for weights at most one (`flat_top_route_h`) to the shifted law, and then splits on the
position of `a` in the flat interval `[1 - β, β]`: at an end, differentiability is part (iii)
of that theorem; strictly inside, the shifted shape is linear on a neighbourhood
(`differentiableAt_quadrantExtension_on_flat_interval`). The shifted shape and the original
shape differ by a multiple of the level, which does not change differentiability.

## Main results

- `differentiableAt_of_top_flat`: differentiability at a direction where the top-indicator
  passage times grow at the maximal rate.

## References

- C. Janjigian, F. Rassoul-Agha and T. Seppäläinen, *Differentiability of the shape function in
  the planar corner growth model*, preprint, Theorem 2.2.
- Georgiou, Rassoul-Agha and Seppäläinen (manuscript in preparation), the flat-edge theorem.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

namespace LPPDifferentiability

/-- **Differentiability at a point of the flat segment.** Let `μ` be a non-degenerate
weight law with a finite negative moment of order above one, and let `g` be its shape (continuous,
homogeneous, concave, almost sure uniform shape law). Let `a` be in `(0, 1)`. If the expected
passage times of the indicator of the sites at the top of the support, divided by `m`, tend to
`1` along the floors of `(m a, m (1 - a))`, then the quadrant extension of `g` is
differentiable at `(a, 1 - a)`.

This is Theorem 2.2 of the differentiability preprint, for a general weight law; it is derived
from the case of weights at most one (`flat_top_route_h`) by the flat-cone theorem and the shift
adapters. -/
theorem differentiableAt_of_top_flat
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hnondegenerate : ∀ c : ℝ, μ ({c} : Set ℝ) < 1)
    (hneg : ∃ pneg : ℝ, 1 < pneg ∧
      (∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ pneg) ∂μ) < ∞)
    (g : Quadrant → ℝ) (hgcont : Continuous g)
    (hghom : ∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x)
    (hgconc : ∀ (x y : Quadrant) (r t : ℝ≥0), r + t = 1 →
      (r : ℝ) * g x + (t : ℝ) * g y ≤ g (r * x.1 + t * y.1, r * x.2 + t * y.2))
    (hgshape : ∀ᵐ ω ∂environmentLaw μ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage ω 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ))
    (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1)
    (htop : Tendsto (fun m : ℕ => (∫ ω : Environment, lastPassage (fun z =>
      if (ω z : EReal) = sSup ((fun t : ℝ => (t : EReal)) '' μ.support) then (1 : ℝ) else 0)
        0 (⌊(m : ℝ) * a⌋₊, ⌊(m : ℝ) * (1 - a)⌋₊) ∂environmentLaw μ) / (m : ℝ))
      atTop (𝓝 1)) :
    DifferentiableAt ℝ (quadrantExtension g) (a, 1 - a) := by
  classical
  -- a positive limit forces a positive atom at the top of the support, and a real top value
  have hatom := source_top_atom_pos_of_top_limit_pos μ a 1 htop one_pos
  obtain ⟨M, hM, hupper, hMatom⟩ := source_top_real_of_atom_pos μ hatom
  -- the shifted law
  obtain ⟨ν, hν⟩ : ∃ ν : Measure ℝ, ν = μ.map (fun x : ℝ => x + (1 - M)) := ⟨_, rfl⟩
  have : IsProbabilityMeasure ν := by
    rw [hν]
    exact (Measure.isProbabilityMeasure_map_iff
      (by fun_prop : Measurable (fun x : ℝ => x + (1 - M))).aemeasurable).2 inferInstance
  obtain ⟨-, -, hle, hν1⟩ := shifted_law_environment μ M hM ν hν
  have hp₀ : 0 < ν {1} := by
    rw [hν1, hMatom]
    exact hatom
  have hp₁ : ν {1} < 1 := by
    rw [hν1]
    exact hnondegenerate M
  obtain ⟨hnegν, hbcont, hbhom, hbconc, hbshape⟩ :=
    shifted_shape_of_shape μ M hupper hneg ν hν g hgcont hghom hgconc hgshape
  obtain ⟨gtop, htcont, hthom, htconc, htshape, hlim⟩ :=
    exists_top_shape_of_shifted_law μ M hM ν hν
  -- the top shape is `1` at the direction
  have hqa : ((toQuadrant (a, 1 - a)).1 : ℝ) = a := Real.coe_toNNReal a ha₀.le
  have hqb : ((toQuadrant (a, 1 - a)).2 : ℝ) = 1 - a :=
    Real.coe_toNNReal (1 - a) (by linarith)
  have hgt1 : gtop (toQuadrant (a, 1 - a)) = 1 := by
    have h := hlim (toQuadrant (a, 1 - a))
    rw [hqa, hqb] at h
    exact tendsto_nhds_unique h htop
  -- the flat-segment theorem for the shifted law
  obtain ⟨hF1, hF2, hF3, hF4⟩ := flat_top_route_h ν hle hp₀ hp₁ hnegν
    (fun z : Quadrant => g z + (1 - M) * ((z.1 : ℝ) + z.2)) hbcont hbhom hbconc hbshape
    gtop htcont hthom htconc htshape
  set R : Set ℝ := Set.range fun n : ℕ =>
    (∫ ω, (halfLineEdge ω (n + 1) : ℝ) ∂environmentLaw ν) / ((n : ℝ) + 1) with hR
  have hBdd : BddBelow R := by
    by_contra hnb
    have h := hF1 hnb a ⟨ha₀.le, ha₁.le⟩
    linarith
  obtain ⟨β, hglb⟩ : ∃ β, IsGLB R β := ⟨sInf R, isGLB_csInf (Set.range_nonempty _) hBdd⟩
  obtain ⟨hβhalf, hβone, hiff⟩ := hF2 β hglb
  obtain ⟨hedge1, hedge2⟩ := hF4 β hglb
  have hmem : a ∈ Icc (1 - β) β := (hiff a ⟨ha₀.le, ha₁.le⟩).1 hgt1
  have hlevel : ∀ t ∈ Icc (1 - β) β,
      (fun z : Quadrant => g z + (1 - M) * ((z.1 : ℝ) + z.2)) (toQuadrant (t, 1 - t)) = 1 := by
    intro t ht
    have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact hF3 t ht01 ((hiff t ht01).2 ht)
  have hgb : DifferentiableAt ℝ
      (quadrantExtension (fun z : Quadrant => g z + (1 - M) * ((z.1 : ℝ) + z.2))) (a, 1 - a) := by
    rcases hmem.1.eq_or_lt with h1 | h1
    · have e : 1 - a = β := by linarith
      rw [e, ← h1]
      exact hedge2
    · rcases hmem.2.eq_or_lt with h2 | h2
      · have e : 1 - a = 1 - β := by rw [h2]
        rw [e, h2]
        exact hedge1
      · exact differentiableAt_quadrantExtension_on_flat_interval
          (fun z : Quadrant => g z + (1 - M) * ((z.1 : ℝ) + z.2)) (fun c z => hbhom c z)
          (1 - β) β 1 (by linarith) (by linarith) hβone.le hlevel a ⟨h1, h2⟩
  exact (differentiableAt_quadrantExtension_add_level_iff g (1 - M) (a, 1 - a) ha₀
    (sub_pos.2 ha₁)).1 hgb

end LPPDifferentiability
