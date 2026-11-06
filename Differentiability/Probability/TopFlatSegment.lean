/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.TopShapeBeyondEdge
public import Differentiability.Probability.TopFlatBeyondEdge
public import Differentiability.Probability.FlatShapeAdapters
public import Differentiability.Analysis.SymmetricFlatInterval
public import LPP_Foundations.Frozen.Analysis.ToQuadrant
public import LPP_Foundations.Frozen.Model.Quadrant
import Mathlib.Tactic

/-!
# The flat segment of the top shape

Let `gtop` be the shape function of the top field (the sites of weight `1`), and let `R` be the
set of expected edge rates `E a_{n+1} / (n+1)`. This module proves the dichotomy of the
flat-segment theorem for the top shape:

* if `R` is unbounded below, `gtop (t, 1 - t) < 1` for every `t` in `[0, 1]`;
* if `β` is the greatest lower bound of `R`, then `1/2 ≤ β < 1` and `gtop (t, 1 - t) = 1`
  exactly for `t` in `[1 - β, β]`.

The proof has four ingredients:

* the strict bound beyond the edge is used at a point of `R` below an intermediate speed;
* the existence of a direction with value `1` at or beyond the edge speed rules out the
  case that `gtop < 1` everywhere on the segment;
* the symmetry (swap) and the axis value `gtop (1, 0) = ν {1} < 1` let the theorem on
  symmetric concave profiles (`symmetric_flat_interval`) describe the equality set as one
  interval `[1 - b, b]`;
* the two one-sided facts then force `b = β`.

## Main results

- `gtop_flat_segment_route_h`: the description of the flat segment of the top shape.

## References

- Georgiou, Rassoul-Agha and Seppäläinen (manuscript in preparation), the flat-edge theorem.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

namespace LPPDifferentiability

/-- The first coordinate of the quadrant point of `(x, 1 - x)` is `x` when `0 ≤ x`. -/
private theorem toQuadrant_fst_coe (x : ℝ) (h : 0 ≤ x) :
    ((toQuadrant (x, 1 - x)).1 : ℝ) = x :=
  Real.coe_toNNReal _ h

/-- The second coordinate of the quadrant point of `(x, 1 - x)` is `1 - x` when `x ≤ 1`. -/
private theorem toQuadrant_snd_coe (x : ℝ) (h : x ≤ 1) :
    ((toQuadrant (x, 1 - x)).2 : ℝ) = 1 - x :=
  Real.coe_toNNReal _ (sub_nonneg.2 h)

/-- **The flat segment of the top shape.** Let the weight law `ν` have an atom at `1`
of mass strictly between `0` and `1`, and let `gtop` be a continuous, homogeneous, concave
function that is the almost sure uniform shape of the top passage time. Let `R` be the set of
expected half-line edge rates `E a_{n+1} / (n+1)`. If `R` is unbounded below, then `gtop`
is below `1` at every `(t, 1 - t)` with `t` in `[0, 1]`. If `β` is the greatest lower bound of
`R`, then `1/2 ≤ β < 1`, and for `t` in `[0, 1]`, `gtop (t, 1 - t) = 1` holds exactly when
`t` lies in `[1 - β, β]`.

This is the flat-segment description in the flat-edge theorem of Georgiou, Rassoul-Agha and
Seppäläinen (manuscript in preparation). The proof combines the strict bound beyond the edge,
the existence of a value-one direction at or beyond the edge speed, the shape adapters
(swap symmetry, axis value, bound by the level) and `symmetric_flat_interval`. -/
theorem gtop_flat_segment_route_h (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hp₀ : 0 < ν {1}) (hp₁ : ν {1} < 1)
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
    (¬ BddBelow R → ∀ t ∈ Icc (0 : ℝ) 1, gtop (toQuadrant (t, 1 - t)) < 1) ∧
    (∀ β : ℝ, IsGLB R β → 1 / 2 ≤ β ∧ β < 1 ∧
      ∀ t ∈ Icc (0 : ℝ) 1, (gtop (toQuadrant (t, 1 - t)) = 1 ↔ t ∈ Icc (1 - β) β)) := by
  classical
  intro R
  -- the profile along the segment, with its defining equation
  obtain ⟨f, hf⟩ : ∃ f : ℝ → ℝ, ∀ t, f t = gtop (toQuadrant (t, 1 - t)) :=
    ⟨fun t => gtop (toQuadrant (t, 1 - t)), fun _ => rfl⟩
  -- The strict bound beyond the edge, in the form used below: one element of `R` below `c`
  -- gives `f s < 1` for `s > c`
  have hN6 : ∀ (c : ℝ) (n : ℕ),
      (∫ ω, (halfLineEdge ω (n + 1) : ℝ) ∂environmentLaw ν) / ((n : ℝ) + 1) < c →
      ∀ s : ℝ, c < s → 0 ≤ s → s ≤ 1 → f s < 1 := by
    intro c n hn s hcs hs₀ hs₁
    rw [hf]
    refine gtop_lt_one_beyond_edge ν hp₀ hp₁ gtop htcont hthom htconc htshape c (n + 1)
      (Nat.succ_pos n) ?_ s hcs hs₀ hs₁
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [div_lt_iff₀ hpos] at hn
    push_cast
    exact hn
  refine ⟨?_, ?_⟩
  · -- `R` unbounded below
    intro hunb t ht
    obtain ⟨r, hrR, hrlt⟩ : ∃ r ∈ R, r < t - 1 := by
      by_contra hcon
      apply hunb
      refine ⟨t - 1, fun r hr => ?_⟩
      by_contra hlt
      exact hcon ⟨r, hr, lt_of_not_ge hlt⟩
    obtain ⟨n, hn⟩ := hrR
    have h := hN6 (t - 1) n (hn.trans_lt hrlt) t (by linarith) ht.1 ht.2
    rw [hf] at h
    exact h
  · -- `β` is the greatest lower bound of `R`
    intro β hβ
    have hq : Continuous fun x : ℝ => toQuadrant (x, 1 - x) :=
      (continuous_real_toNNReal.comp continuous_id).prodMk
        (continuous_real_toNNReal.comp (continuous_const.sub continuous_id))
    have hfcont : Continuous f := by
      have h : f = fun x : ℝ => gtop (toQuadrant (x, 1 - x)) := funext hf
      rw [h]
      exact htcont.comp hq
    -- shape adapters
    have hadapt := expected_floor_limit_of_top_shape_block ν gtop htcont hthom htconc htshape
    have hupper : ∀ t ∈ Icc (0 : ℝ) 1, f t ≤ 1 := by
      intro t ht
      have h := (hadapt.2.2.1 (toQuadrant (t, 1 - t))).2
      rw [toQuadrant_fst_coe t ht.1, toQuadrant_snd_coe t ht.2] at h
      rw [hf]
      linarith
    have hsym : ∀ t ∈ Icc (0 : ℝ) 1, f (1 - t) = f t := by
      intro t _
      have hswap := shape_swap_of_coordinatewise_field ν
        (fun t : ℝ => if t = 1 then (1 : ℝ) else 0)
        (Measurable.ite (measurableSet_singleton 1) measurable_const measurable_const)
        gtop htcont hthom htshape (toQuadrant (t, 1 - t))
      have e : toQuadrant (1 - t, 1 - (1 - t)) =
          ((toQuadrant (t, 1 - t)).2, (toQuadrant (t, 1 - t)).1) := by
        simp only [toQuadrant, sub_sub_cancel]
      rw [hf, hf, e]
      exact hswap
    have hend : f 1 < 1 := by
      have haxis := hadapt.2.2.2
      have hlt : ν.real {1} < 1 := by
        have h := (ENNReal.toReal_lt_toReal (measure_ne_top ν {1}) ENNReal.one_ne_top).2 hp₁
        simpa [Measure.real] using h
      have e : toQuadrant (1, 1 - 1) = ((1 : ℝ≥0), (0 : ℝ≥0)) := by
        simp [toQuadrant]
      rw [hf, e, haxis]
      exact hlt
    have hconc : ConcaveOn ℝ (Icc (0 : ℝ) 1) f := by
      refine ⟨convex_Icc 0 1, ?_⟩
      intro x hx y hy a b ha hb hab
      have hz : a * x + b * y ∈ Icc (0 : ℝ) 1 := by
        have h := (convex_Icc (0 : ℝ) 1) hx hy ha hb hab
        simpa only [smul_eq_mul] using h
      have hsum : a.toNNReal + b.toNNReal = 1 := by
        apply NNReal.eq
        rw [NNReal.coe_add, Real.coe_toNNReal _ ha, Real.coe_toNNReal _ hb, NNReal.coe_one]
        exact hab
      have h := htconc (toQuadrant (x, 1 - x)) (toQuadrant (y, 1 - y)) a.toNNReal b.toNNReal hsum
      have e : (a.toNNReal * (toQuadrant (x, 1 - x)).1 + b.toNNReal * (toQuadrant (y, 1 - y)).1,
          a.toNNReal * (toQuadrant (x, 1 - x)).2 + b.toNNReal * (toQuadrant (y, 1 - y)).2) =
          toQuadrant (a * x + b * y, 1 - (a * x + b * y)) := by
        refine Prod.ext (NNReal.eq ?_) (NNReal.eq ?_)
        · simp only [NNReal.coe_add, NNReal.coe_mul, toQuadrant_fst_coe x hx.1,
            toQuadrant_fst_coe y hy.1, toQuadrant_fst_coe (a * x + b * y) hz.1,
            Real.coe_toNNReal _ ha, Real.coe_toNNReal _ hb]
        · simp only [NNReal.coe_add, NNReal.coe_mul, toQuadrant_snd_coe x hx.2,
            toQuadrant_snd_coe y hy.2, toQuadrant_snd_coe (a * x + b * y) hz.2,
            Real.coe_toNNReal _ ha, Real.coe_toNNReal _ hb]
          linarith
      rw [e, Real.coe_toNNReal _ ha, Real.coe_toNNReal _ hb] at h
      simp only [smul_eq_mul, hf]
      exact h
    -- a direction `x₀ ≥ β` with `f x₀ = 1`
    obtain ⟨x₀, hx₀0, hβx₀, hx₀1, hx₀⟩ :=
      exists_gtop_eq_one_ge_edgeSpeed ν hp₀ hp₁ gtop htcont hthom htconc htshape β hβ
    have hfx₀ : f x₀ = 1 := by rw [hf]; exact hx₀
    rcases symmetric_flat_interval hfcont.continuousOn hconc hupper hsym hend with
      hlt | ⟨b, ⟨hb₁, hb₂, hbc⟩, -⟩
    · exfalso
      have h := hlt x₀ ⟨hx₀0, hx₀1⟩
      rw [hfx₀] at h
      exact lt_irrefl _ h
    · have hx₀b : x₀ ≤ b := ((hbc x₀ ⟨hx₀0, hx₀1⟩).1 hfx₀).2
      have hβb : β ≤ b := le_trans hβx₀ hx₀b
      have hbβ : b ≤ β := by
        by_contra hcon
        have hlt : β < b := lt_of_not_ge hcon
        obtain ⟨r, hrR, hrlt⟩ := hβ.exists_between (show β < (β + b) / 2 by linarith)
        obtain ⟨n, hn⟩ := hrR
        have hb0 : 0 ≤ b := by linarith
        have hb1 : b ≤ 1 := hb₂.le
        have h := hN6 ((β + b) / 2) n (hn.trans_lt hrlt.2) b (by linarith) hb0 hb1
        have hfb : f b = 1 :=
          (hbc b ⟨hb0, hb1⟩).2 ⟨by linarith, le_refl b⟩
        rw [hfb] at h
        exact lt_irrefl _ h
      have hbeq : b = β := le_antisymm hbβ hβb
      refine ⟨by rw [← hbeq]; exact hb₁, by rw [← hbeq]; exact hb₂, fun t ht => ?_⟩
      have h := hbc t ht
      rw [hbeq, hf t] at h
      exact h

end LPPDifferentiability
