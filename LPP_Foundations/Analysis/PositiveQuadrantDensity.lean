/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.Quadrant
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Positive rational approximation in the quadrant

The interior is a subtype of the closed quadrant.
Rational brackets are chosen coordinate by coordinate, using ordinary rational density.
-/

@[expose] public section

open scoped NNReal NNRat Topology
open Filter

namespace LPPDifferentiability

/-- Points of the existing quadrant with both coordinates positive. -/
abbrev QuadrantInterior := {x : Quadrant // 0 < x.1 ∧ 0 < x.2}

/-- Nonnegative rational pairs with both coordinates positive. -/
abbrev NNRatPairInterior := {q : ℚ≥0 × ℚ≥0 // 0 < q.1 ∧ 0 < q.2}

/-- The canonical coordinatewise cast, defined on every nonnegative rational pair. -/
def nnratPairToQuadrant (q : ℚ≥0 × ℚ≥0) : Quadrant := (q.1, q.2)

/-- Each component is the real rational value with its nonnegativity proof. -/
theorem nnratPairToQuadrant_eq (q : ℚ≥0 × ℚ≥0) :
    nnratPairToQuadrant q =
      (⟨(q.1 : ℝ), NNRat.cast_nonneg q.1⟩,
       ⟨(q.2 : ℝ), NNRat.cast_nonneg q.2⟩) := rfl

@[simp] theorem nnratPairToQuadrant_fst (q : ℚ≥0 × ℚ≥0) :
    (nnratPairToQuadrant q).1 = (q.1 : ℝ≥0) := rfl

@[simp] theorem nnratPairToQuadrant_snd (q : ℚ≥0 × ℚ≥0) :
    (nnratPairToQuadrant q).2 = (q.2 : ℝ≥0) := rfl

@[simp] theorem coe_nnratPairToQuadrant_fst (q : ℚ≥0 × ℚ≥0) :
    ((nnratPairToQuadrant q).1 : ℝ) = (q.1 : ℝ) := rfl

@[simp] theorem coe_nnratPairToQuadrant_snd (q : ℚ≥0 × ℚ≥0) :
    ((nnratPairToQuadrant q).2 : ℝ) = (q.2 : ℝ) := rfl

private theorem exists_nnrat_bracket (x : ℝ≥0) (hx : 0 < x)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ l u : ℚ≥0, 0 < l ∧ 0 < u ∧ (l : ℝ≥0) ≤ x ∧ x ≤ (u : ℝ≥0) ∧
      dist (l : ℝ≥0) x < ε ∧ dist (u : ℝ≥0) x < ε := by
  have hxR : 0 < (x : ℝ) := hx
  obtain ⟨a, ha, hax⟩ := exists_rat_btwn (max_lt hxR (sub_lt_self _ hε))
  obtain ⟨b, hxb, hb⟩ := exists_rat_btwn (lt_add_of_pos_right (x : ℝ) hε)
  have ha0 : 0 < a := Rat.cast_pos.mp ((le_max_left _ _).trans_lt ha)
  have hb0 : 0 < b := Rat.cast_pos.mp (hxR.trans hxb)
  let l : ℚ≥0 := ⟨a, ha0.le⟩
  let u : ℚ≥0 := ⟨b, hb0.le⟩
  have hl : (l : ℝ≥0) ≤ x := by
    change (a : ℝ) ≤ (x : ℝ)
    exact hax.le
  have hu : x ≤ (u : ℝ≥0) := by
    change (x : ℝ) ≤ (b : ℝ)
    exact hxb.le
  refine ⟨l, u, ha0, hb0, hl, hu, ?_, ?_⟩
  · change |(a : ℝ) - (x : ℝ)| < ε
    rw [abs_of_neg (sub_neg.mpr hax)]
    have h := (le_max_right _ _).trans_lt ha
    linarith only [h]
  · change |(b : ℝ) - (x : ℝ)| < ε
    rw [abs_of_pos (sub_pos.mpr hxb)]
    linarith only [hb]

/-- Every interior point has positive rational lower and upper brackets arbitrarily
close in the product maximum metric. The inequalities hold in each coordinate. -/
theorem exists_positive_rational_brackets (x : QuadrantInterior) (ε : ℝ) (hε : 0 < ε) :
    ∃ l u : NNRatPairInterior,
      nnratPairToQuadrant l.val ≤ x.val ∧ x.val ≤ nnratPairToQuadrant u.val ∧
      dist (nnratPairToQuadrant l.val) x.val < ε ∧
      dist (nnratPairToQuadrant u.val) x.val < ε := by
  obtain ⟨l₁, u₁, hl₁, hu₁, hlx₁, hxu₁, hld₁, hud₁⟩ :=
    exists_nnrat_bracket x.val.1 x.property.1 ε hε
  obtain ⟨l₂, u₂, hl₂, hu₂, hlx₂, hxu₂, hld₂, hud₂⟩ :=
    exists_nnrat_bracket x.val.2 x.property.2 ε hε
  refine ⟨⟨(l₁, l₂), hl₁, hl₂⟩, ⟨(u₁, u₂), hu₁, hu₂⟩,
    ⟨hlx₁, hlx₂⟩, ⟨hxu₁, hxu₂⟩, ?_, ?_⟩
  · exact max_lt hld₁ hld₂
  · exact max_lt hud₁ hud₂

/-- Every interior point is approached from below and above by positive rational
pairs, with both coordinatewise brackets valid at every natural index. -/
theorem exists_positive_rational_bracketing_sequences (x : QuadrantInterior) :
    ∃ l u : ℕ → NNRatPairInterior,
      (∀ n, nnratPairToQuadrant (l n).val ≤ x.val ∧
        x.val ≤ nnratPairToQuadrant (u n).val) ∧
      Tendsto (fun n => nnratPairToQuadrant (l n).val) atTop (𝓝 x.val) ∧
      Tendsto (fun n => nnratPairToQuadrant (u n).val) atTop (𝓝 x.val) := by
  have hbrackets (n : ℕ) := exists_positive_rational_brackets x
    (1 / ((n : ℝ) + 1)) (by positivity)
  choose l u hl hu hld hud using hbrackets
  have hzero : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hconverges (v : ℕ → NNRatPairInterior)
      (hv : ∀ n, dist (nnratPairToQuadrant (v n).val) x.val < 1 / ((n : ℝ) + 1)) :
      Tendsto (fun n => nnratPairToQuadrant (v n).val) atTop (𝓝 x.val) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have heventually := hzero.eventually (gt_mem_nhds hε)
    filter_upwards [heventually] with n hn
    exact (hv n).trans hn
  exact ⟨l, u, fun n => ⟨hl n, hu n⟩, hconverges l hld, hconverges u hud⟩

/-- The cast does not identify distinct rational pairs. -/
theorem nnratPairToQuadrant_injective : Function.Injective nnratPairToQuadrant := by
  intro p q hpq
  apply Prod.ext
  · apply (NNRat.cast_injective (α := ℝ))
    exact congrArg (fun x : Quadrant => (x.1 : ℝ)) hpq
  · apply (NNRat.cast_injective (α := ℝ))
    exact congrArg (fun x : Quadrant => (x.2 : ℝ)) hpq

end LPPDifferentiability
