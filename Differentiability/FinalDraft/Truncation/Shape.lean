/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.Truncation.Laws
public import LPP_Foundations.Frozen.Analysis.ClosedUnitDirections
public import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Differentiability.FinalDraft.Truncation.Passage
import Martin2004.Analysis.RationalPassageNormalization
import Martin2004.Probability.RealExpectedTruncation
import Martin2004.Probability.WeakNegativeShape
import ProbabilityBasics.Probability.PositiveMomentTail
import Mathlib.Tactic

/-! The quantitative upper-truncation bound in the final differentiability
draft, subsection `sub:ub_mom-chat`, interpreted on the closed unit segment of Section 2, subsection `sub:shape`. -/

public section

open MeasureTheory Filter Set
open scoped Topology NNReal

namespace LPPDifferentiability.FinalDraft.Truncation

private theorem exists_shape_and_expectedRate (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : LPPStatements.HasNegativePartMomentAbove μ 1)
    (hpos : LPPStatements.HasSqrtUpperTail μ) :
    ∃ g : Quadrant → ℝ,
      LPPStatements.IsShapeFunction μ g ∧ LPPStatements.IsExpectedRateShape μ g := by
  obtain ⟨g, ⟨hc, hh, hconc, hae, hrate, _⟩, _⟩ :=
    exists_unique_shape_with_expected_rate_of_negative_moment_and_positive_tail μ hneg hpos
  exact ⟨g, ⟨hc, hh, hconc,
    (LPPStatements.approximatesLastPassage_iff_positive_threshold μ g).mpr hae⟩, hrate⟩

/-- The sample shape for the actual clipped law also approximates its
coupled field on the probability space of the original weights.
This is the clipped shape used in subsection `sub:ub_mom-chat`. -/
theorem ae_upperClippedField_approximates_shape (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (M : ℝ) (g : Quadrant → ℝ) (hg : LPPStatements.IsShapeFunction (upperClippedLaw μ M) g) :
    ∀ᵐ ω ∂environmentLaw μ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage (upperClippedField M ω) 0 d -
          g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤ ε * ((d.1 + d.2 : ℕ) : ℝ) :=
  (measurePreserving_upperClippedField μ M).quasiMeasurePreserving.ae hg.2.2.2

/-- A single universal constant bounds the loss of the actual shape after
upper clipping. The whole-quadrant bound is proportional to the direction's
taxicab norm. On the closed unit segment the unscaled bound gives uniform
convergence, as in subsection `sub:ub_mom-chat` of the final differentiability draft. -/
theorem exists_upperClipped_shape_comparison :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
      LPPStatements.HasNegativePartMomentAbove μ 1 →
      LPPStatements.HasSqrtUpperTail μ →
      ∃ (g : Quadrant → ℝ) (gM : ℝ → Quadrant → ℝ),
        LPPStatements.IsShapeFunction μ g ∧
        (∀ M : ℝ, LPPStatements.IsShapeFunction (upperClippedLaw μ M) (gM M)) ∧
        (∀ (M : ℝ) (x : Quadrant), 0 ≤ g x - gM M x ∧
          g x - gM M x ≤ C * LPPStatements.taxicabNorm x * (upperTail μ M).toReal) ∧
        (∀ (M : ℝ) (x : Quadrant), x ∈ closedUnitDirections →
          0 ≤ g x - gM M x ∧ g x - gM M x ≤ C * (upperTail μ M).toReal) ∧
        TendstoUniformlyOn gM g atTop closedUnitDirections := by
  obtain ⟨C, hC, hfinite⟩ := exists_integral_lastPassage_upperClippedLaw_bound
  refine ⟨C, hC, ?_⟩
  intro μ _ hneg hpos
  have hμ := integrable_id_of_negative_moment_and_positive_tail μ hneg hpos
  -- Take the actual shapes together with their floor expectation limits.
  obtain ⟨g, hg, hgRate⟩ := exists_shape_and_expectedRate μ hneg hpos
  have hex (M : ℝ) : ∃ q : Quadrant → ℝ,
      LPPStatements.IsShapeFunction (upperClippedLaw μ M) q ∧
      LPPStatements.IsExpectedRateShape (upperClippedLaw μ M) q :=
    exists_shape_and_expectedRate (upperClippedLaw μ M)
      (hasNegativePartMomentAbove_upperClippedLaw μ hneg M)
      (hasSqrtUpperTail_upperClippedLaw μ hpos M)
  choose gM hgM hgMRate using hex
  have hcompare (M : ℝ) (x : Quadrant) : 0 ≤ g x - gM M x ∧
      g x - gM M x ≤ C * LPPStatements.taxicabNorm x * (upperTail μ M).toReal := by
    let d (n : ℕ) : ℕ × ℕ :=
      (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
    let gap (n : ℕ) : ℝ :=
      (∫ ω : Environment, lastPassage ω 0 (d n) ∂environmentLaw μ) -
        (∫ ω : Environment, lastPassage ω 0 (d n) ∂environmentLaw (upperClippedLaw μ M))
    have hlim : Tendsto (fun n : ℕ => gap n / (n : ℝ)) atTop (𝓝 (g x - gM M x)) := by
      simpa only [gap, d, sub_div] using (hgRate x).sub (hgMRate M x)
    have hlen := tendsto_floor_pair_length (x.1 : ℝ) (x.2 : ℝ) x.1.coe_nonneg x.2.coe_nonneg
    constructor
    · apply le_of_tendsto_of_tendsto' tendsto_const_nhds hlim
      intro n
      exact div_nonneg (hfinite μ hμ hpos M (d n)).1 (Nat.cast_nonneg n)
    · have hupper : g x - gM M x ≤
          ((x.1 : ℝ) + x.2) * (C * (upperTail μ M).toReal) := by
        apply le_of_tendsto_of_tendsto' hlim (hlen.mul_const (C * (upperTail μ M).toReal))
        intro n
        change gap n / (n : ℝ) ≤
          (((d n).1 + (d n).2 : ℕ) : ℝ) / (n : ℝ) * (C * (upperTail μ M).toReal)
        rw [← mul_div_right_comm]
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
        simpa only [gap, mul_comm, mul_left_comm, mul_assoc] using
          (hfinite μ hμ hpos M (d n)).2
      calc
        _ ≤ _ := hupper
        _ = _ := by unfold LPPStatements.taxicabNorm; ring
  -- The taxicab factor is one on the closed unit segment.
  have hunit (M : ℝ) (x : Quadrant) (hx : x ∈ closedUnitDirections) :
      0 ≤ g x - gM M x ∧ g x - gM M x ≤ C * (upperTail μ M).toReal := by
    have hlen : LPPStatements.taxicabNorm x = 1 := hx
    exact ⟨(hcompare M x).1, by simpa only [hlen, mul_one] using (hcompare M x).2⟩
  refine ⟨g, gM, hg, hgM, hcompare, hunit, ?_⟩
  -- The same tail tends to zero independently of the unit direction.
  have htail : Tendsto (fun M : ℝ => (upperTail μ M).toReal) atTop (𝓝 0) :=
    tendsto_martin_positive_tail_toReal_zero μ hpos
  have hsmall : Tendsto (fun M : ℝ => C * (upperTail μ M).toReal) atTop (𝓝 0) := by
    simpa only [mul_zero] using htail.const_mul C
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(tendsto_order.mp hsmall).2 ε hε] with M hM x hx
  obtain ⟨hn, hb⟩ := hunit M x hx
  rw [Real.dist_eq, abs_of_nonneg hn]
  exact hb.trans_lt hM

/-- The moment assumptions (A2) and (A3) of the paper give the same
quantitative and uniform truncation conclusions in subsection `sub:ub_mom-chat` on the
closed unit segment. -/
theorem exists_upperClipped_shape_comparison_of_paper_moments :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
      LPPStatements.HasNegativePartMomentAbove μ 1 →
      LPPStatements.HasPositivePartMomentAbove μ 4 →
      ∃ (g : Quadrant → ℝ) (gM : ℝ → Quadrant → ℝ),
        LPPStatements.IsShapeFunction μ g ∧
        (∀ M : ℝ, LPPStatements.IsShapeFunction (upperClippedLaw μ M) (gM M)) ∧
        (∀ (M : ℝ) (x : Quadrant), 0 ≤ g x - gM M x ∧
          g x - gM M x ≤ C * LPPStatements.taxicabNorm x * (upperTail μ M).toReal) ∧
        (∀ (M : ℝ) (x : Quadrant), x ∈ closedUnitDirections →
          0 ≤ g x - gM M x ∧ g x - gM M x ≤ C * (upperTail μ M).toReal) ∧
        TendstoUniformlyOn gM g atTop closedUnitDirections := by
  obtain ⟨C, hC, h⟩ := exists_upperClipped_shape_comparison
  exact ⟨C, hC, fun μ _ hneg hpos => h μ hneg
    (positive_integrated_sqrt_tail_lt_top_of_full_positive_moment μ hpos)⟩

end LPPDifferentiability.FinalDraft.Truncation
