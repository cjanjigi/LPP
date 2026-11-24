/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LPP_Foundations.Probability.TruncationTails
public import LPP_Foundations.Statements.ShapeDefinitions
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Tactic

/-! The actual upper-clipped marginal and field used in the truncation
comparison of the final differentiability draft, subsection `sub:ub_mom-chat`. -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace LPPDifferentiability.FinalDraft.Truncation

/-- The law `μ ∧ M` is the image of `μ` under upper clipping at `M`. -/
noncomputable def upperClippedLaw (μ : Measure ℝ) (M : ℝ) : Measure ℝ :=
  μ.map (fun x : ℝ => min M x)

private theorem measurable_clip (M : ℝ) : Measurable (fun x : ℝ => min M x) :=
  measurable_const.min measurable_id

instance instProbabilityMeasureUpperClippedLaw (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (M : ℝ) : IsProbabilityMeasure (upperClippedLaw μ M) :=
  (Measure.isProbabilityMeasure_map_iff (measurable_clip M).aemeasurable).2 inferInstance

/-- Use the original weight at each site to construct its upper-clipped weight. -/
noncomputable def upperClippedField (M : ℝ) (ω : Environment) : Environment :=
  fun z => min M (ω z)

/-- The full clipped field has the canonical independent law of the actual
clipped marginal from the final differentiability draft, subsection `sub:ub_mom-chat`. -/
theorem measurePreserving_upperClippedField (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (M : ℝ) :
    MeasurePreserving (upperClippedField M) (environmentLaw μ)
      (environmentLaw (upperClippedLaw μ M)) :=
  ⟨measurable_coordinatewise_environment_map _ (measurable_clip M),
    environmentLaw_map_coordinatewise μ _ (measurable_clip M)⟩

/-- The integrated upper square-root tail in subsection `sub:ub_mom-chat`, with nonnegative
integrand and a strict upper tail. -/
noncomputable def upperTail (μ : Measure ℝ) (M : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioi M, (μ (Ioi t)) ^ (1 / 2 : ℝ)

/-- Moving the tail cutoff from zero to any finite real number preserves
finiteness of the integral in subsection `sub:ub_mom-chat`. If the cutoff is negative the
extra contribution is bounded by the length of the added interval. -/
theorem upperTail_lt_top (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hpos : LPPStatements.HasSqrtUpperTail μ) (M : ℝ) :
    upperTail μ M < ∞ := by
  let f (t : ℝ) := (μ (Ioi t)) ^ (1 / 2 : ℝ)
  have hsub : Ioi M ⊆ Ioi 0 ∪ Icc M 0 := by
    intro t ht
    by_cases h : 0 < t
    · exact Or.inl h
    · exact Or.inr ⟨(show M < t from ht).le, le_of_not_gt h⟩
  have hfinite : (∫⁻ t in Icc M 0, f t) < ∞ := by
    calc
      _ ≤ ∫⁻ _ in Icc M 0, (1 : ℝ≥0∞) :=
        setLIntegral_mono' measurableSet_Icc fun t _ =>
          ENNReal.rpow_le_one prob_le_one (by norm_num)
      _ < ∞ := by
        rw [setLIntegral_const, Real.volume_Icc]
        exact ENNReal.mul_lt_top ENNReal.one_lt_top ENNReal.ofReal_lt_top
  change (∫⁻ t in Ioi M, f t) < ∞
  calc
    _ ≤ ∫⁻ t in Ioi 0 ∪ Icc M 0, f t := lintegral_mono_set hsub
    _ ≤ (∫⁻ t in Ioi 0, f t) + ∫⁻ t in Icc M 0, f t := lintegral_union_le _ _ _
    _ < ∞ := ENNReal.add_lt_top.2 ⟨hpos, hfinite⟩

/-- Upper clipping can only decrease each strict upper tail, so the clipped
law still meets the upper-tail hypothesis for its shape in subsection `sub:ub_mom-chat`. -/
theorem hasSqrtUpperTail_upperClippedLaw (μ : Measure ℝ)
    (hpos : LPPStatements.HasSqrtUpperTail μ) (M : ℝ) :
    LPPStatements.HasSqrtUpperTail (upperClippedLaw μ M) := by
  unfold LPPStatements.HasSqrtUpperTail at hpos ⊢
  refine lt_of_le_of_lt (lintegral_mono fun t => ?_) hpos
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  rw [upperClippedLaw, Measure.map_apply (measurable_clip M) measurableSet_Ioi]
  apply measure_mono
  intro x hx
  change t < min M x at hx
  exact hx.trans_le (min_le_right M x)

/-- Upper clipping preserves a finite negative-part moment at the same
order. This holds also for negative cutoffs, which contribute a finite
constant to the moment. It supplies (A2) for the clipped law in subsection `sub:ub_mom-chat`. -/
theorem hasNegativePartMomentAbove_upperClippedLaw (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hneg : LPPStatements.HasNegativePartMomentAbove μ 1)
    (M : ℝ) : LPPStatements.HasNegativePartMomentAbove (upperClippedLaw μ M) 1 := by
  obtain ⟨p, hp, hpMoment⟩ := hneg
  let f : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal ((max (-x) 0) ^ p)
  have hf : Measurable f := ENNReal.measurable_ofReal.comp
    ((continuous_id.neg.max continuous_const).rpow_const
      (fun _ => Or.inr (by linarith only [hp] : 0 ≤ p))).measurable
  refine ⟨p, hp, ?_⟩
  change (∫⁻ x, f x ∂μ.map (fun x : ℝ => min M x)) < ∞
  rw [lintegral_map hf (measurable_clip M)]
  have hle (x : ℝ) : f (min M x) ≤ f x + f M := by
    rcases le_total M x with hx | hx
    · rw [min_eq_left hx]
      exact le_add_of_nonneg_left (show 0 ≤ f x from zero_le)
    · rw [min_eq_right hx]
      exact le_add_of_nonneg_right (show 0 ≤ f M from zero_le)
  calc
    _ ≤ ∫⁻ x, f x + f M ∂μ := lintegral_mono hle
    _ = (∫⁻ x, f x ∂μ) + f M := by
      rw [lintegral_add_right (f := f) (g := fun _ => f M) measurable_const,
        lintegral_const, measure_univ, mul_one]
    _ < ∞ := ENNReal.add_lt_top.2 ⟨hpMoment, ENNReal.ofReal_lt_top⟩

end LPPDifferentiability.FinalDraft.Truncation
