/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Analysis.PlanarEntropyModulus
public import LPP_Foundations.Analysis.PositiveQuadrantDensity
import Mathlib.Topology.ContinuousOn
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Conditional real boundary transfer

These deterministic helpers concern one function on the closed quadrant.
Rational estimates, symmetry, and growth are explicit hypotheses; this module
does not construct them, probabilistically or otherwise.
-/

public section

open scoped NNReal NNRat Topology
open Filter

namespace LPPDifferentiability

/-- Transfer the literal rational entropy estimate through interior continuity.
At axes the exact signed formulas suffice; no boundary continuity is assumed. -/
theorem real_boundary_bound_of_rational (g : Quadrant → ℝ) (m L : ℝ)
    (hm : |m| ≤ L)
    (hg : Continuous (fun x : QuadrantInterior => g x.val))
    (haxis₁ : ∀ h : ℝ≥0, g (h, 0) = (h : ℝ) * m)
    (haxis₂ : ∀ t : ℝ≥0, g (0, t) = (t : ℝ) * m)
    (hq : ∀ q : ℚ≥0 × ℚ≥0,
      |g (nnratPairToQuadrant q) - (q.2 : ℝ) * m| ≤
        (q.1 : ℝ) * L + 8 * L * Real.sqrt (((q.1 : ℝ) + q.2) *
          (((q.1 : ℝ) + q.2) * Real.log ((q.1 : ℝ) + q.2) -
            (q.1 : ℝ) * Real.log q.1 - (q.2 : ℝ) * Real.log q.2)))
    (h t : ℝ≥0) :
    |g (h, t) - (t : ℝ) * m| ≤
      (h : ℝ) * L + 8 * L * Real.sqrt (((h : ℝ) + t) *
        (((h : ℝ) + t) * Real.log ((h : ℝ) + t) -
          (h : ℝ) * Real.log h - (t : ℝ) * Real.log t)) := by
  by_cases hh : h = 0
  · subst h
    simp only [haxis₂, sub_self, abs_zero, NNReal.coe_zero, zero_add,
      zero_mul, sub_zero, mul_zero, add_zero, Real.sqrt_zero, le_refl]
  by_cases ht : t = 0
  · subst t
    simp only [haxis₁, NNReal.coe_zero, zero_mul, sub_zero, add_zero,
      sub_self, Real.sqrt_zero, mul_zero, abs_mul, abs_of_nonneg h.coe_nonneg]
    exact mul_le_mul_of_nonneg_left hm h.coe_nonneg
  let x : QuadrantInterior := ⟨(h, t), pos_iff_ne_zero.mpr hh, pos_iff_ne_zero.mpr ht⟩
  obtain ⟨l, u, _, hl, _⟩ := exists_positive_rational_bracketing_sequences x
  let v : ℕ → QuadrantInterior := fun n =>
    ⟨nnratPairToQuadrant (l n).val, by
      constructor
      · exact NNRat.cast_pos.mpr (l n).property.1
      · exact NNRat.cast_pos.mpr (l n).property.2⟩
  have hv : Tendsto v atTop (𝓝 x) := tendsto_subtype_rng.mpr hl
  have hleft := ((hg.continuousAt.tendsto.comp hv).sub
    (((NNReal.continuous_coe.comp continuous_snd).continuousAt.tendsto.comp hl).mul_const m)).abs
  have hrhs : Continuous (fun p : Quadrant => (p.1 : ℝ) * L +
      8 * L * Real.sqrt (((p.1 : ℝ) + p.2) *
        (((p.1 : ℝ) + p.2) * Real.log ((p.1 : ℝ) + p.2) -
          (p.1 : ℝ) * Real.log p.1 - (p.2 : ℝ) * Real.log p.2))) :=
    ((NNReal.continuous_coe.comp continuous_fst).mul_const L).add
      (continuous_const.mul ((((NNReal.continuous_coe.comp continuous_fst).add
        (NNReal.continuous_coe.comp continuous_snd)).mul continuous_planar_entropy).sqrt))
  exact le_of_tendsto_of_tendsto hleft (hrhs.continuousAt.tendsto.comp hl)
    (Filter.Eventually.of_forall (fun n => hq (l n).val))

/-- One positive radius works on the entire closed bounded vertical face. -/
theorem exists_uniform_vertical_boundary_delta (g : Quadrant → ℝ) (m L : ℝ)
    (hL : 0 ≤ L)
    (haxis : ∀ t : ℝ≥0, g (0, t) = (t : ℝ) * m)
    (hb : ∀ h t : ℝ≥0, |g (h, t) - (t : ℝ) * m| ≤
      (h : ℝ) * L + 8 * L * Real.sqrt (((h : ℝ) + t) *
        (((h : ℝ) + t) * Real.log ((h : ℝ) + t) -
          (h : ℝ) * Real.log h - (t : ℝ) * Real.log t)))
    (R ε : ℝ) (hR : 0 < R) (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∀ h : ℝ≥0, h ≤ δ → ∀ t : ℝ≥0,
      (t : ℝ) ≤ R → |g (h, t) - g (0, t)| < ε := by
  obtain ⟨δ, hδ, hd⟩ := exists_planar_boundary_delta L R hL hR ε hε
  exact ⟨δ, hδ, fun h hh t ht => by
    rw [haxis]
    exact (hb h t).trans_lt (hd h hh t ht)⟩

/-- Same-function coordinate symmetry supplies the other face with the same
radius, simultaneously for all points of either bounded face. -/
theorem exists_uniform_both_boundary_delta (g : Quadrant → ℝ)
    (hsymm : ∀ h t : ℝ≥0, g (h, t) = g (t, h))
    (hv : ∀ R ε : ℝ, 0 < R → 0 < ε →
      ∃ δ : ℝ≥0, 0 < δ ∧ ∀ h : ℝ≥0, h ≤ δ → ∀ t : ℝ≥0,
        (t : ℝ) ≤ R → |g (h, t) - g (0, t)| < ε)
    (R ε : ℝ) (hR : 0 < R) (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∀ h : ℝ≥0, h ≤ δ → ∀ t : ℝ≥0,
      (t : ℝ) ≤ R →
        |g (h, t) - g (0, t)| < ε ∧ |g (t, h) - g (t, 0)| < ε := by
  obtain ⟨δ, hδ, hd⟩ := hv R ε hR hε
  refine ⟨δ, hδ, fun h hh t ht => ⟨hd h hh t ht, ?_⟩⟩
  rw [hsymm t h, hsymm t 0]
  exact hd h hh t ht

private theorem continuousAt_vertical_of_uniform (g : Quadrant → ℝ) (m : ℝ)
    (haxis : ∀ t : ℝ≥0, g (0, t) = (t : ℝ) * m)
    (hv : ∀ R ε : ℝ, 0 < R → 0 < ε →
      ∃ δ : ℝ≥0, 0 < δ ∧ ∀ h : ℝ≥0, h ≤ δ → ∀ t : ℝ≥0,
        (t : ℝ) ≤ R → |g (h, t) - g (0, t)| < ε)
    (t₀ : ℝ≥0) : ContinuousAt g (0, t₀) := by
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := hv ((t₀ : ℝ) + 1) (ε / 2) (by positivity) (half_pos hε)
  let d : ℝ := min (δ : ℝ) (min 1 (ε / (2 * (|m| + 1))))
  have hden : 0 < 2 * (|m| + 1) := by positivity
  have hdpos : 0 < d := lt_min hδ (lt_min zero_lt_one (div_pos hε hden))
  refine ⟨d, hdpos, ?_⟩
  intro y hy
  have h₁ : dist y.1 0 < d := (le_max_left _ _).trans_lt hy
  have h₂ : dist y.2 t₀ < d := (le_max_right _ _).trans_lt hy
  have hy₁ : y.1 ≤ δ := by
    have h := h₁.trans_le (min_le_left _ _)
    apply NNReal.coe_le_coe.mp
    simpa only [NNReal.dist_eq, NNReal.coe_zero, sub_zero,
      abs_of_nonneg y.1.coe_nonneg] using h.le
  have ht : (y.2 : ℝ) ≤ (t₀ : ℝ) + 1 := by
    have h := h₂.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    rw [NNReal.dist_eq] at h
    linarith only [(le_abs_self ((y.2 : ℝ) - t₀)).trans_lt h]
  have hsmall : |(y.2 : ℝ) - t₀| < ε / (2 * (|m| + 1)) :=
    h₂.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hmul : |(y.2 : ℝ) - t₀| * |m| < ε / 2 := by
    have h := (lt_div_iff₀ hden).mp hsmall
    nlinarith only [h, abs_nonneg ((y.2 : ℝ) - t₀)]
  rw [Real.dist_eq]
  calc
    |g y - g (0, t₀)| ≤ |g y - g (0, y.2)| + |g (0, y.2) - g (0, t₀)| :=
      abs_sub_le _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hd y.1 hy₁ y.2 ht) (by
      rw [haxis, haxis, ← sub_mul, abs_mul]
      exact hmul)
    _ = ε := by ring

/-- Interior and both face estimates give closed-quadrant continuity. The
origin uses the separately supplied linear growth bound. Each premise here is
an assumption until the probabilistic construction supplies it. -/
theorem continuous_quadrant_of_uniform_faces_and_growth (g : Quadrant → ℝ)
    (m L : ℝ) (hL : 0 ≤ L)
    (hg : Continuous (fun x : QuadrantInterior => g x.val))
    (haxis₁ : ∀ h : ℝ≥0, g (h, 0) = (h : ℝ) * m)
    (haxis₂ : ∀ t : ℝ≥0, g (0, t) = (t : ℝ) * m)
    (hv : ∀ R ε : ℝ, 0 < R → 0 < ε →
      ∃ δ : ℝ≥0, 0 < δ ∧ ∀ h : ℝ≥0, h ≤ δ → ∀ t : ℝ≥0,
        (t : ℝ) ≤ R → |g (h, t) - g (0, t)| < ε)
    (hh : ∀ R ε : ℝ, 0 < R → 0 < ε →
      ∃ δ : ℝ≥0, 0 < δ ∧ ∀ h : ℝ≥0, h ≤ δ → ∀ t : ℝ≥0,
        (t : ℝ) ≤ R → |g (t, h) - g (t, 0)| < ε)
    (hgrowth : ∀ x : Quadrant, |g x| ≤ L * ((x.1 : ℝ) + x.2)) :
    Continuous g := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx₁ : x.1 = 0
  · by_cases hx₂ : x.2 = 0
    · have hx : x = (0, 0) := Prod.ext hx₁ hx₂
      subst x
      apply Metric.continuousAt_iff.mpr
      intro ε hε
      have hden : 0 < 2 * (L + 1) := by positivity
      refine ⟨ε / (2 * (L + 1)), div_pos hε hden, ?_⟩
      intro y hy
      have h₁ : (y.1 : ℝ) < ε / (2 * (L + 1)) := by
        have h := (le_max_left _ _).trans_lt hy
        simpa only [NNReal.dist_eq, NNReal.coe_zero, sub_zero,
          abs_of_nonneg y.1.coe_nonneg] using h
      have h₂ : (y.2 : ℝ) < ε / (2 * (L + 1)) := by
        have h := (le_max_right _ _).trans_lt hy
        simpa only [NNReal.dist_eq, NNReal.coe_zero, sub_zero,
          abs_of_nonneg y.2.coe_nonneg] using h
      rw [Real.dist_eq, haxis₂, NNReal.coe_zero, zero_mul, sub_zero]
      have ha := (lt_div_iff₀ hden).mp h₁
      have hb := (lt_div_iff₀ hden).mp h₂
      have hc := hgrowth y
      nlinarith only [ha, hb, hc, y.1.coe_nonneg, y.2.coe_nonneg]
    · have hx : x = (0, x.2) := Prod.ext hx₁ rfl
      rw [hx]
      exact continuousAt_vertical_of_uniform g m haxis₂ hv x.2
  · by_cases hx₂ : x.2 = 0
    · have hs := continuousAt_vertical_of_uniform (fun y => g (y.2, y.1)) m haxis₁ hh x.1
      have hs' : ContinuousAt (fun y : Quadrant => g (y.2, y.1)) (x.2, x.1) := by
        simpa only [hx₂] using hs
      have hc := hs'.comp (continuous_snd.prodMk continuous_fst).continuousAt
        (x := x)
      have he : ((fun y : Quadrant => g (y.2, y.1)) ∘
          (fun y : Quadrant => (y.2, y.1))) = g := by
        funext y
        rcases y with ⟨a, b⟩
        rfl
      rw [he] at hc
      exact hc
    · have hs : IsOpen {y : Quadrant | 0 < y.1 ∧ 0 < y.2} :=
        (isOpen_lt (α := ℝ≥0) (β := Quadrant) continuous_const
          continuous_fst).inter
          (isOpen_lt (α := ℝ≥0) (β := Quadrant) continuous_const
            continuous_snd)
      exact ((continuousOn_iff_continuous_domRestrict.mpr hg) x
        ⟨pos_iff_ne_zero.mpr hx₁, pos_iff_ne_zero.mpr hx₂⟩).continuousAt
          (hs.mem_nhds ⟨pos_iff_ne_zero.mpr hx₁, pos_iff_ne_zero.mpr hx₂⟩)

/-- The deterministic assembly from the exact rational estimate to full
continuity. Rational control, symmetry of the function, and linear growth must
still be supplied separately; they are not proved here. -/
theorem continuous_quadrant_of_rational_boundary_and_symmetry
    (g : Quadrant → ℝ) (m L : ℝ) (hm : |m| ≤ L)
    (hg : Continuous (fun x : QuadrantInterior => g x.val))
    (haxis₁ : ∀ h : ℝ≥0, g (h, 0) = (h : ℝ) * m)
    (haxis₂ : ∀ t : ℝ≥0, g (0, t) = (t : ℝ) * m)
    (hq : ∀ q : ℚ≥0 × ℚ≥0,
      |g (nnratPairToQuadrant q) - (q.2 : ℝ) * m| ≤
        (q.1 : ℝ) * L + 8 * L * Real.sqrt (((q.1 : ℝ) + q.2) *
          (((q.1 : ℝ) + q.2) * Real.log ((q.1 : ℝ) + q.2) -
            (q.1 : ℝ) * Real.log q.1 - (q.2 : ℝ) * Real.log q.2)))
    (hsymm : ∀ h t : ℝ≥0, g (h, t) = g (t, h))
    (hgrowth : ∀ x : Quadrant, |g x| ≤ L * ((x.1 : ℝ) + x.2)) :
    Continuous g := by
  have hL : 0 ≤ L := (abs_nonneg m).trans hm
  have hb := real_boundary_bound_of_rational g m L hm hg haxis₁ haxis₂ hq
  have hv := exists_uniform_vertical_boundary_delta g m L hL haxis₂ hb
  have hh (R ε : ℝ) (hR : 0 < R) (hε : 0 < ε) :
      ∃ δ : ℝ≥0, 0 < δ ∧ ∀ h : ℝ≥0, h ≤ δ → ∀ t : ℝ≥0,
        (t : ℝ) ≤ R → |g (t, h) - g (t, 0)| < ε := by
    obtain ⟨δ, hδ, hd⟩ := exists_uniform_both_boundary_delta g hsymm hv R ε hR hε
    exact ⟨δ, hδ, fun h hh t ht => (hd h hh t ht).2⟩
  exact continuous_quadrant_of_uniform_faces_and_growth g m L hL hg haxis₁ haxis₂ hv hh hgrowth

end LPPDifferentiability
