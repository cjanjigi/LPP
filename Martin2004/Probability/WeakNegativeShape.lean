/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.NegativeMomentBounds
public import Martin2004.Probability.MartinWeakContinuity
public import Martin2004.Probability.WeakUniformUpper
public import Martin2004.Probability.WeakUniformLower
public import LPP_Foundations.Shape.Uniqueness
public import LPP_Foundations.Statements.ShapeDefinitions
import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Shape assembly under a negative moment above one

The negative moment and the positive integrated square-root tail produce the first
moment and the unique continuous homogeneous concave expected rate. The upper and
directed lower sample laws concern that same witness. Their common event gives the
uniform absolute error law over all natural endpoints, including both axes.
-/

public section

open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

namespace LPPDifferentiability

/-- A finite negative-part moment above one and the positive integrated
square-root tail give a first moment for the signed marginal. -/
theorem integrable_id_of_negative_moment_and_positive_tail
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : LPPStatements.HasNegativePartMomentAbove μ 1)
    (hpos : LPPStatements.HasSqrtUpperTail μ) :
    LPPStatements.HasFiniteMean μ := by
  obtain ⟨p, hp, hmoment⟩ := hneg
  have hn := integrable_negativePart_of_lintegral_lt_top μ p hp hmoment
  have hpTail : (∫⁻ t in Ioi (0 : ℝ), μ (Ioi t)) < ∞ := by
    apply lt_of_le_of_lt _ hpos
    apply lintegral_mono
    intro t
    calc
      μ (Ioi t) = (μ (Ioi t)) ^ (1 : ℝ) := (ENNReal.rpow_one _).symm
      _ ≤ (μ (Ioi t)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow_of_exponent_ge prob_le_one (by norm_num)
  have hpIntegrable : Integrable (fun t : ℝ => max t 0) μ := by
    refine ⟨(measurable_id.max measurable_const).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun t : ℝ => le_max_right t 0)]
    rw [lintegral_eq_lintegral_meas_lt μ
      (Filter.Eventually.of_forall fun t : ℝ => le_max_right t 0)
      (measurable_id.max measurable_const).aemeasurable]
    convert hpTail using 1
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    congr 1
    ext x
    simp only [mem_ofPred_eq, mem_Ioi, lt_max_iff,
      not_lt.mpr (le_of_lt ht), or_false]
  change Integrable (fun t : ℝ => t) μ
  convert hpIntegrable.sub hn using 1
  ext t
  dsimp
  rcases le_total 0 t with ht | ht
  · rw [max_eq_left ht, max_eq_right (neg_nonpos.mpr ht), sub_zero]
  · rw [max_eq_right ht, max_eq_left (neg_nonneg.mpr ht), zero_sub, neg_neg]

/-- The floor expectations determine a unique continuous homogeneous concave shape
under the weak negative moment. This is an expected-rate
existence theorem; it does not assume or assert a uniform sample limit. -/
theorem exists_unique_continuous_expected_shape_of_negative_moment_and_positive_tail
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : LPPStatements.HasNegativePartMomentAbove μ 1)
    (hpos : LPPStatements.HasSqrtUpperTail μ) :
    ∃! g : Quadrant → ℝ,
      Continuous g ∧
      LPPStatements.IsHomogeneous g ∧
      LPPStatements.IsConcaveOnQuadrant g ∧
      LPPStatements.IsExpectedRateShape μ g ∧
      (∀ d : ℕ × ℕ, Integrable (fun ω : Environment => lastPassage ω 0 d)
        (environmentLaw μ)) := by
  have hμ := integrable_id_of_negative_moment_and_positive_tail μ hneg hpos
  obtain ⟨g, hg, _hUnique⟩ :=
    exists_unique_continuous_lastPassage_real_expected_rate_of_integrable_and_positive_tail
      μ hμ hpos
  refine ⟨g, ⟨hg.2, ?_, ?_, hg.1.1.1, hg.1.1.2.2.2.2.2.2⟩, ?_⟩
  · intro c x
    exact hg.1.2.1 c x
  · intro x y a b _hab
    have h := hg.1.2.2.1 (a • x) (b • y)
    rw [hg.1.2.1 a x, hg.1.2.1 b y] at h
    exact h
  · intro f hf
    funext x
    exact tendsto_nhds_unique (hf.2.2.2.1 x) (hg.1.1.1 x)

/-- The same expected rate gives the uniform absolute passage law on one
original-environment event, for every positive real tolerance. The expected
characterization and finite passage integrability are kept. -/
theorem exists_unique_shape_with_expected_rate_of_negative_moment_and_positive_tail
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : LPPStatements.HasNegativePartMomentAbove μ 1)
    (hpos : LPPStatements.HasSqrtUpperTail μ) :
    ∃! g : Quadrant → ℝ,
      Continuous g ∧
      LPPStatements.IsHomogeneous g ∧
      LPPStatements.IsConcaveOnQuadrant g ∧
      (∀ᵐ ω ∂environmentLaw μ, ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
          |lastPassage ω 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
            ε * ((d.1 + d.2 : ℕ) : ℝ)) ∧
      LPPStatements.IsExpectedRateShape μ g ∧
      (∀ d : ℕ × ℕ, Integrable (fun ω : Environment => lastPassage ω 0 d)
        (environmentLaw μ)) := by
  have hμ := integrable_id_of_negative_moment_and_positive_tail μ hneg hpos
  obtain ⟨g, hg, _hUniqueExpected⟩ :=
    exists_unique_continuous_expected_shape_of_negative_moment_and_positive_tail μ hneg hpos
  obtain ⟨p, hp, hmoment⟩ := hneg
  have hu := ae_eventually_lastPassage_uniform_upper_of_integrable_and_positive_tail
    μ hμ hpos g hg.2.2.2.1
  have hl := ae_eventually_lastPassage_uniform_lower_of_negative_moment
    μ hμ hpos p hp hmoment g hg.1 (fun c x => hg.2.1 c x) hg.2.2.2.1
  have hae : ∀ᵐ ω ∂environmentLaw μ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage ω 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ) := by
    filter_upwards [hu, hl] with ω hωu hωl
    intro ε hε
    obtain ⟨Nu, hNu, hupper⟩ := hωu ε hε
    obtain ⟨Nl, _hNl, hlower⟩ := hωl ε hε
    refine ⟨max Nu Nl, hNu.trans (le_max_left _ _), ?_⟩
    intro d hd
    have hup := hupper d ((le_max_left _ _).trans hd)
    have hlo := hlower d ((le_max_right _ _).trans hd)
    exact abs_le.mpr ⟨by linarith only [hlo], hup⟩
  refine ⟨g, ⟨hg.1, hg.2.1, hg.2.2.1, hae, hg.2.2.2.1, hg.2.2.2.2⟩, ?_⟩
  intro f hf
  funext x
  exact tendsto_nhds_unique (hf.2.2.2.2.1 x) (hg.2.2.2.1 x)

/-- The weak-negative uniform shape theorem. The only premises are a
probability marginal, a negative-part moment above one and the positive
integrated square-root tail. Uniqueness is among all continuous homogeneous
sample-shape candidates, without an expected-rate premise for a competitor. -/
theorem exists_unique_shape_of_negative_moment_and_positive_tail
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : LPPStatements.HasNegativePartMomentAbove μ 1)
    (hpos : LPPStatements.HasSqrtUpperTail μ) :
    ∃! g : Quadrant → ℝ,
      Continuous g ∧
      LPPStatements.IsHomogeneous g ∧
      LPPStatements.IsConcaveOnQuadrant g ∧
      (∀ᵐ ω ∂environmentLaw μ, ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
          |lastPassage ω 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
            ε * ((d.1 + d.2 : ℕ) : ℝ)) := by
  obtain ⟨g, hg, _hUniqueExpected⟩ :=
    exists_unique_shape_with_expected_rate_of_negative_moment_and_positive_tail μ hneg hpos
  refine ⟨g, ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.1⟩, ?_⟩
  intro f hf
  exact shapeCandidates_eq μ f g hf.1 hg.1 hf.2.1 hg.2.1
    ((LPPStatements.approximatesLastPassage_iff_positive_threshold μ f).mpr hf.2.2.2)
    ((LPPStatements.approximatesLastPassage_iff_positive_threshold μ g).mpr hg.2.2.2.1)

end LPPDifferentiability
