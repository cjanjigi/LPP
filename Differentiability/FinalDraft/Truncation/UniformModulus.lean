/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.Truncation.Shape
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Differentiability.Paper.Setting
import LPP_Foundations.Analysis.HomogeneousDifferentiability
import LPP_Foundations.Shape.Uniqueness
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic

/-! The conditional implication in subsection `sub:ub_mom-chat` of the final differentiability
draft. The premise is a first-order remainder bound with a radius shared by
all cutoffs, for each specified error tolerance. -/

public section

open Filter MeasureTheory
open scoped Topology NNReal

namespace LPPDifferentiability.FinalDraft.Truncation

/-- A local pointwise limit of real functions with a common first-order
remainder bound at zero is differentiable there. The slopes converge as
a consequence of the bound. This is the real-variable step in subsection `sub:ub_mom-chat`. -/
theorem exists_hasDerivAt_of_uniform_firstOrder_remainder
    (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ) (slopes : ℕ → ℝ) (r : ℝ) (hr : 0 < r)
    (hpoint : ∀ h : ℝ, |h| < r → Tendsto (fun n => F n h) atTop (𝓝 (f h)))
    (hmod : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (h : ℝ), |h| < δ →
      |F n h - F n 0 - slopes n * h| ≤ ε * |h|) :
    ∃ d : ℝ, Tendsto slopes atTop (𝓝 d) ∧ HasDerivAt f d 0 := by
  have hzero : Tendsto (fun n => F n 0) atTop (𝓝 (f 0)) :=
    hpoint 0 (by simpa only [abs_zero] using hr)
  -- One fixed secant approximates all slopes at this tolerance.
  have hcauchy : CauchySeq slopes := by
    refine Metric.cauchySeq_iff.mpr fun ε hε => ?_
    obtain ⟨δ, hδ, hbound⟩ := hmod (ε / 4) (by positivity)
    let h := min r δ / 2
    have hh : 0 < h := half_pos (lt_min hr hδ)
    have hsmall : |h| < min r δ := by
      rw [abs_of_pos hh]
      exact half_lt_self (lt_min hr hδ)
    have hhr : |h| < r := hsmall.trans_le (min_le_left _ _)
    have hhδ : |h| < δ := hsmall.trans_le (min_le_right _ _)
    let q (n : ℕ) := (F n h - F n 0) / h
    have hq : Tendsto q atTop (𝓝 ((f h - f 0) / h)) :=
      ((hpoint h hhr).sub hzero).div_const h
    have hclose (n : ℕ) : |q n - slopes n| ≤ ε / 4 := by
      have heq : q n - slopes n = (F n h - F n 0 - slopes n * h) / h := by
        dsimp only [q]
        rw [sub_div (F n h - F n 0) (slopes n * h) h, mul_div_cancel_right₀ _ hh.ne']
      rw [heq, abs_div, abs_of_pos hh, div_le_iff₀ hh]
      simpa only [abs_of_pos hh] using hbound n h hhδ
    -- The chosen secants converge, so their pairwise differences vanish.
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hq.cauchySeq (ε / 4) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hmn := hN m hm n hn
    rw [Real.dist_eq] at hmn ⊢
    have htriangle : |slopes m - slopes n| ≤
        |q m - slopes m| + |q m - q n| + |q n - slopes n| := by
      calc
        _ ≤ |slopes m - q m| + |q m - slopes n| := abs_sub_le _ _ _
        _ ≤ _ := by
          rw [abs_sub_comm (slopes m) (q m)]
          linarith only [abs_sub_le (q m) (q n) (slopes n)]
    linarith only [htriangle, hclose m, hclose n, hmn, hε]
  obtain ⟨d, hd⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨d, hd, ?_⟩
  -- At each fixed increment the first-order inequality survives the limit.
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := hmod ε hε
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (lt_min hr hδ)] with h hh
  have hsmall : |h| < min r δ := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hh
  have hlim := (((hpoint h (hsmall.trans_le (min_le_left _ _))).sub hzero).sub
    (hd.mul_const h)).abs
  have hrem : |f h - f 0 - d * h| ≤ ε * |h| :=
    le_of_tendsto hlim (Eventually.of_forall fun n => hbound n h
      (hsmall.trans_le (min_le_right _ _)))
  simpa only [sub_zero, smul_eq_mul, Real.norm_eq_abs, mul_comm h d] using hrem

private theorem actual_shapes_eq {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {g k : Quadrant → ℝ} (hg : LPPStatements.IsShapeFunction μ g)
    (hk : LPPStatements.IsShapeFunction μ k) : g = k :=
  shapeCandidates_eq μ g k hg.1 hk.1 hg.2.1 hk.2.1 hg.2.2.2 hk.2.2.2

private theorem actual_upperClipped_shapes_tendstoUniformlyOn
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : LPPStatements.HasNegativePartMomentAbove μ 1)
    (hpos : LPPStatements.HasSqrtUpperTail μ)
    (g : Quadrant → ℝ) (gM : ℝ → Quadrant → ℝ)
    (hg : LPPStatements.IsShapeFunction μ g)
    (hgM : ∀ M : ℝ, LPPStatements.IsShapeFunction (upperClippedLaw μ M) (gM M)) :
    TendstoUniformlyOn gM g atTop closedUnitDirections := by
  obtain ⟨_, _, hcomparison⟩ := exists_upperClipped_shape_comparison
  obtain ⟨k, kM, hk, hkM, _, _, hlim⟩ := hcomparison μ hneg hpos
  have heq : gM = kM := funext fun M => actual_shapes_eq (hgM M) (hkM M)
  rwa [actual_shapes_eq hg hk, heq]

/-- At an interior unit direction, a common first-order remainder for
the actual clipped shapes forces the original shape to be differentiable
there. The shared-radius condition is the premise of subsection `sub:ub_mom-chat`.
Natural cutoffs suffice because they tend to infinity. -/
theorem differentiableAt_shape_of_uniform_upperClipped_remainder
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : LPPStatements.HasNegativePartMomentAbove μ 1)
    (hpos : LPPStatements.HasSqrtUpperTail μ)
    (g : Quadrant → ℝ) (gM : ℝ → Quadrant → ℝ)
    (hg : LPPStatements.IsShapeFunction μ g)
    (hgM : ∀ M : ℝ, LPPStatements.IsShapeFunction (upperClippedLaw μ M) (gM M))
    (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) (slopes : ℕ → ℝ)
    (hmod : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (h : ℝ), |h| < δ →
      |quadrantExtension (gM (n : ℝ)) (a + h, 1 - a - h) -
        quadrantExtension (gM (n : ℝ)) (a, 1 - a) - slopes n * h| ≤ ε * |h|) :
    ∃ d : ℝ, Tendsto slopes atTop (𝓝 d) ∧
      HasDerivAt (fun h : ℝ => quadrantExtension g (a + h, 1 - a - h)) d 0 ∧
      DifferentiableAt ℝ (quadrantExtension g) (a, 1 - a) := by
  have hlim := actual_upperClipped_shapes_tendstoUniformlyOn μ hneg hpos g gM hg hgM
  let r := min a (1 - a)
  have hr : 0 < r := lt_min ha₀ (sub_pos.mpr ha₁)
  let F (n : ℕ) (h : ℝ) := quadrantExtension (gM (n : ℝ)) (a + h, 1 - a - h)
  let f (h : ℝ) := quadrantExtension g (a + h, 1 - a - h)
  -- Small transverse increments stay in the closed unit segment.
  have hpoint (h : ℝ) (hh : |h| < r) : Tendsto (fun n => F n h) atTop (𝓝 (f h)) := by
    obtain ⟨hl, hu⟩ := abs_lt.mp hh
    have hleft : 0 ≤ a + h := by linarith only [hl, min_le_left a (1 - a)]
    have hright : 0 ≤ 1 - a - h := by linarith only [hu, min_le_right a (1 - a)]
    have hm : toQuadrant (a + h, 1 - a - h) ∈ closedUnitDirections := by
      change (((a + h).toNNReal : ℝ) + ((1 - a - h).toNNReal : ℝ)) = 1
      rw [Real.coe_toNNReal _ hleft, Real.coe_toNNReal _ hright]
      ring
    exact (hlim.tendsto_at hm).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  have hrema : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (h : ℝ), |h| < δ →
      |F n h - F n 0 - slopes n * h| ≤ ε * |h| := by
    simpa only [F, add_zero, sub_zero] using hmod
  obtain ⟨d, hslopes, hd⟩ :=
    exists_hasDerivAt_of_uniform_firstOrder_remainder F f slopes r hr hpoint hrema
  exact ⟨d, hslopes, hd, (differentiableAt_profile_iff_quadrantExtension g hg.2.1 a ha₀ ha₁).mp
    hd.differentiableAt⟩

/-- If the shared-radius condition in subsection `sub:ub_mom-chat` holds at every interior
unit direction, the original shape is differentiable throughout the
open quadrant. The radius may depend on the direction. -/
theorem shape_differentiable_of_uniform_upperClipped_remainder
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : LPPStatements.HasNegativePartMomentAbove μ 1)
    (hpos : LPPStatements.HasSqrtUpperTail μ)
    (g : Quadrant → ℝ) (gM : ℝ → Quadrant → ℝ)
    (hg : LPPStatements.IsShapeFunction μ g)
    (hgM : ∀ M : ℝ, LPPStatements.IsShapeFunction (upperClippedLaw μ M) (gM M))
    (hmod : ∀ a : ℝ, 0 < a → a < 1 → ∃ slopes : ℕ → ℝ,
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (h : ℝ), |h| < δ →
        |quadrantExtension (gM (n : ℝ)) (a + h, 1 - a - h) -
          quadrantExtension (gM (n : ℝ)) (a, 1 - a) - slopes n * h| ≤ ε * |h|) :
    LPPStatements.DifferentiableOnOpenQuadrant g := by
  apply (Paper.differentiable_on_unit_segment_iff_open_quadrant g hg.2.1).mp
  intro a ha₀ ha₁
  obtain ⟨slopes, hrema⟩ := hmod a ha₀ ha₁
  obtain ⟨_, _, _, hd⟩ :=
    differentiableAt_shape_of_uniform_upperClipped_remainder μ hneg hpos g gM hg hgM
      a ha₀ ha₁ slopes hrema
  exact hd

end LPPDifferentiability.FinalDraft.Truncation
