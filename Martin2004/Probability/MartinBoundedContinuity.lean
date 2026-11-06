/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.RealExpectedRateGeometry
public import Martin2004.Probability.BoundedNaturalBoundary
public import Martin2004.Analysis.BoundedRealBoundaryTransfer
public import Martin2004.Probability.BoundedMarginalTails
public import ProbabilityBasics.Analysis.PlanarEntropyModulus

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Bounded expected-rate continuity

The bounded-law theorem retains the unique expected-rate witness and
all its geometry, then proves continuity on the whole closed quadrant. Its
rational estimate is produced by positive common-denominator normalization;
no compatibility of independently chosen rate functions is assumed.
-/

public section

open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal NNRat

namespace LPPDifferentiability

/-- The entropy boundary expression is homogeneous of degree one.
The square root scales linearly because both its factors have degree one.
Zero scales and axis coordinates are included. -/
theorem planar_boundary_expression_mul (L : ℝ) (c h t : ℝ≥0) :
    (c * h : ℝ≥0) * L + 8 * L * Real.sqrt
      ((((c * h : ℝ≥0) : ℝ) + (c * t : ℝ≥0)) *
        ((((c * h : ℝ≥0) : ℝ) + (c * t : ℝ≥0)) *
            Real.log (((c * h : ℝ≥0) : ℝ) + (c * t : ℝ≥0)) -
          (c * h : ℝ≥0) * Real.log (c * h : ℝ≥0) -
          (c * t : ℝ≥0) * Real.log (c * t : ℝ≥0))) =
      (c : ℝ) * ((h : ℝ) * L + 8 * L * Real.sqrt
        (((h : ℝ) + t) * (((h : ℝ) + t) * Real.log ((h : ℝ) + t) -
          (h : ℝ) * Real.log h - (t : ℝ) * Real.log t))) := by
  rw [planar_entropy_mul]
  simp only [NNReal.coe_mul]
  have hp : ((c : ℝ) * h + (c : ℝ) * t) *
      ((c : ℝ) * (((h : ℝ) + t) * Real.log ((h : ℝ) + t) -
        (h : ℝ) * Real.log h - (t : ℝ) * Real.log t)) =
      (c : ℝ) ^ 2 * (((h : ℝ) + t) *
        (((h : ℝ) + t) * Real.log ((h : ℝ) + t) -
          (h : ℝ) * Real.log h - (t : ℝ) * Real.log t)) := by ring
  rw [hp, Real.sqrt_mul (sq_nonneg (c : ℝ)), Real.sqrt_sq c.coe_nonneg]
  ring

/-- A positive common denominator transports the natural entropy boundary
bound to the same represented rational rate, including axes and the origin.
The mean and rate values may be signed. -/
theorem nnrat_boundary_bound_of_natural_representation
    (G : (ℕ × ℕ) → ℝ) (F : (ℚ≥0 × ℚ≥0) → ℝ) (m L : ℝ)
    (hF : ∀ d : ℕ, 0 < d → ∀ a : ℕ × ℕ,
      F ((a.1 : ℚ≥0) / d, (a.2 : ℚ≥0) / d) = G a / (d : ℝ))
    (hG : ∀ a b : ℕ,
      |G (a, b) - (b : ℝ) * m| ≤ (a : ℝ) * L +
        8 * L * Real.sqrt (((a : ℝ) + b) *
          (((a : ℝ) + b) * Real.log ((a : ℝ) + b) -
            (a : ℝ) * Real.log a - (b : ℝ) * Real.log b)))
    (q : ℚ≥0 × ℚ≥0) :
    |F q - (q.2 : ℝ) * m| ≤ (q.1 : ℝ) * L +
      8 * L * Real.sqrt (((q.1 : ℝ) + q.2) *
        (((q.1 : ℝ) + q.2) * Real.log ((q.1 : ℝ) + q.2) -
          (q.1 : ℝ) * Real.log q.1 - (q.2 : ℝ) * Real.log q.2)) := by
  obtain ⟨d, hd, a, rfl⟩ := nnrat_pair_exists_nat_div q
  rw [hF d hd a]
  simp only [NNRat.cast_div, NNRat.cast_natCast]
  have hs := planar_boundary_expression_mul L ((d : ℝ≥0)⁻¹)
    (a.1 : ℝ≥0) (a.2 : ℝ≥0)
  simp only [NNReal.coe_mul, NNReal.coe_inv, NNReal.coe_natCast] at hs
  have hs' : (a.1 : ℝ) / d * L + 8 * L * Real.sqrt
      (((a.1 : ℝ) / d + (a.2 : ℝ) / d) *
        (((a.1 : ℝ) / d + (a.2 : ℝ) / d) *
            Real.log ((a.1 : ℝ) / d + (a.2 : ℝ) / d) -
          ((a.1 : ℝ) / d) * Real.log ((a.1 : ℝ) / d) -
          ((a.2 : ℝ) / d) * Real.log ((a.2 : ℝ) / d))) =
      ((a.1 : ℝ) * L + 8 * L * Real.sqrt (((a.1 : ℝ) + a.2) *
        (((a.1 : ℝ) + a.2) * Real.log ((a.1 : ℝ) + a.2) -
          (a.1 : ℝ) * Real.log a.1 - (a.2 : ℝ) * Real.log a.2))) / d := by
    simpa only [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hs
  rw [hs', ← mul_div_right_comm, ← sub_div,
    abs_div, abs_of_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  exact div_le_div_of_nonneg_right (hG a.1 a.2) (Nat.cast_nonneg d)

/-- Expected floor limits and natural-ray limits force the
positive-denominator representation for the same displayed real witness.
The corrected expectation is monotone even for a signed marginal mean. -/
theorem real_expected_rate_rational_natural_representation
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) (g : Quadrant → ℝ)
    (hlim : ∀ x : Quadrant, Tendsto (fun n : ℕ =>
      (∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
        ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (g x)))
    (G : (ℕ × ℕ) → ℝ)
    (hG : ∀ a : ℕ × ℕ, Tendsto (fun n : ℕ =>
      (∫ ω : Environment, lastPassage ω 0 (n • a) ∂environmentLaw μ) /
        (n : ℝ)) atTop (𝓝 (G a)))
    (d : ℕ) (hd : 0 < d) (a : ℕ × ℕ) :
    g (nnratPairToQuadrant ((a.1 : ℚ≥0) / d, (a.2 : ℚ≥0) / d)) =
      G a / (d : ℝ) := by
  have hmono : Monotone (fun z : ℕ × ℕ =>
      (∫ ω : Environment, lastPassage ω 0 z ∂environmentLaw μ) -
        ((z.1 + z.2 : ℕ) : ℝ) * (∫ x : ℝ, x ∂μ)) := by
    intro z w hzw
    exact integral_lastPassage_corrected_monotone μ hμ z w hzw.1 hzw.2
  have ht := tendsto_rational_floor_of_corrected_ray
    (fun z => ∫ ω : Environment, lastPassage ω 0 z ∂environmentLaw μ)
    (∫ x : ℝ, x ∂μ) hmono a d hd (G a) (hG a)
  have hg := hlim (nnratPairToQuadrant
    ((a.1 : ℚ≥0) / d, (a.2 : ℚ≥0) / d))
  simp only [coe_nnratPairToQuadrant_fst, coe_nnratPairToQuadrant_snd,
    NNRat.cast_div, NNRat.cast_natCast, ← mul_div_assoc] at hg
  exact tendsto_nhds_unique hg ht

/-- A bounded probability law determines one unique expected rate
on the whole existing quadrant, with all its expectation and geometry
properties retained. The same witness is globally continuous and has the
entropy bound and one common radius for both bounded closed faces.
Only the probability law, a nonnegative support radius and its almost-sure
absolute bound are premises; no boundary continuity or rate compatibility
is supplied by the caller. -/
theorem exists_unique_continuous_lastPassage_real_expected_rate_of_ae_abs_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (L : ℝ) (hL : 0 ≤ L)
    (hμ : ∀ᵐ x ∂μ, |x| ≤ L) :
    ∃! g : Quadrant → ℝ,
      (
      ((∀ x : Quadrant, Tendsto (fun n : ℕ =>
        (∫ ω : Environment, lastPassage ω 0
          (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
          ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (g x))) ∧
      Continuous (fun x : QuadrantInterior => g x.val) ∧
      g 0 = 0 ∧
      (∀ s : ℝ≥0, g (s, 0) = (∫ t : ℝ, t ∂μ) * (s : ℝ)) ∧
      (∀ t : ℝ≥0, g (0, t) = (∫ s : ℝ, s ∂μ) * (t : ℝ)) ∧
      (∃ F : (ℚ≥0 × ℚ≥0) → ℝ,
        (∀ q : ℚ≥0 × ℚ≥0, Tendsto (fun n : ℕ =>
          (∫ ω : Environment, lastPassage ω 0
            (⌊(n : ℝ) * (q.1 : ℝ)⌋₊, ⌊(n : ℝ) * (q.2 : ℝ)⌋₊)
            ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (F q))) ∧
        (∀ q : ℚ≥0 × ℚ≥0, g (nnratPairToQuadrant q) = F q)) ∧
      (∀ z : ℕ × ℕ, Integrable (fun ω : Environment => lastPassage ω 0 z)
        (environmentLaw μ))) ∧
      (∀ (c : ℝ≥0) (x : Quadrant), g (c • x) = (c : ℝ) * g x) ∧
      (∀ x y : Quadrant, g x + g y ≤ g (x + y)) ∧
      (∀ x : Quadrant, g x.swap = g x) ∧
      (∀ (L : ℝ), 0 ≤ L → (∀ᵐ t ∂μ, |t| ≤ L) →
        ∀ x : Quadrant, |g x| ≤ L * ((x.1 : ℝ) + x.2))) ∧
      Continuous g ∧
      (∀ h t : ℝ≥0,
        |g (h, t) - (t : ℝ) * (∫ x : ℝ, x ∂μ)| ≤
          (h : ℝ) * L + 8 * L * Real.sqrt (((h : ℝ) + t) *
            (((h : ℝ) + t) * Real.log ((h : ℝ) + t) -
              (h : ℝ) * Real.log h - (t : ℝ) * Real.log t))) ∧
      (∀ R ε : ℝ, 0 < R → 0 < ε →
        ∃ δ : ℝ≥0, 0 < δ ∧ ∀ h : ℝ≥0, h ≤ δ → ∀ t : ℝ≥0,
          (t : ℝ) ≤ R →
            |g (h, t) - g (0, t)| < ε ∧ |g (t, h) - g (t, 0)| < ε) := by
  have hneg := lt_of_le_of_lt
    (integrated_negative_sqrt_tail_le_of_ae_abs_le μ L hL hμ)
    (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top : ENNReal.ofReal L < ∞)
  have hpos := lt_of_le_of_lt
    (integrated_positive_sqrt_tail_le_of_ae_abs_le μ L hL hμ)
    (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top : ENNReal.ofReal L < ∞)
  obtain ⟨g, hg, hUnique⟩ :=
    exists_unique_lastPassage_real_expected_rate_geometry_of_martin_tails μ hneg hpos
  obtain ⟨G, ⟨hG, hGB⟩, _⟩ :=
    exists_unique_lastPassage_natural_shape_of_ae_abs_le μ L hL hμ
  have hrep := real_expected_rate_rational_natural_representation μ
    (integrable_id_of_ae_abs_le μ L hμ) g hg.1.1 G (fun a => (hG.1 a).1)
  have hq (q : ℚ≥0 × ℚ≥0) :
      |g (nnratPairToQuadrant q) - (q.2 : ℝ) * (∫ x : ℝ, x ∂μ)| ≤
        (q.1 : ℝ) * L + 8 * L * Real.sqrt (((q.1 : ℝ) + q.2) *
          (((q.1 : ℝ) + q.2) * Real.log ((q.1 : ℝ) + q.2) -
            (q.1 : ℝ) * Real.log q.1 - (q.2 : ℝ) * Real.log q.2)) := by
    apply nnrat_boundary_bound_of_natural_representation G
      (fun q => g (nnratPairToQuadrant q)) (∫ x : ℝ, x ∂μ) L hrep ?_ q
    intro a b
    simpa only [Nat.cast_add] using hGB a b
  have hx (h : ℝ≥0) : g (h, 0) = (h : ℝ) * (∫ x : ℝ, x ∂μ) := by
    simpa only [mul_comm] using hg.1.2.2.2.1 h
  have hy (t : ℝ≥0) : g (0, t) = (t : ℝ) * (∫ x : ℝ, x ∂μ) := by
    simpa only [mul_comm] using hg.1.2.2.2.2.1 t
  have hsymm (h t : ℝ≥0) : g (h, t) = g (t, h) :=
    (hg.2.2.2.1 (h, t)).symm
  have hm := abs_integral_id_le_of_ae_abs_le μ L hL hμ
  have hb := real_boundary_bound_of_rational g (∫ x : ℝ, x ∂μ) L hm
    hg.1.2.1 hx hy hq
  have hv := exists_uniform_vertical_boundary_delta g (∫ x : ℝ, x ∂μ) L
    hL hy hb
  have hboth := exists_uniform_both_boundary_delta g hsymm hv
  have hc := continuous_quadrant_of_rational_boundary_and_symmetry g
    (∫ x : ℝ, x ∂μ) L hm hg.1.2.1 hx hy hq hsymm
    (hg.2.2.2.2 L hL hμ)
  refine ⟨g, ⟨hg, hc, hb, hboth⟩, ?_⟩
  intro f hf
  exact hUnique f hf.1

end LPPDifferentiability
