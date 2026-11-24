/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.Truncation.Laws
import Differentiability.Full.Differentiability
import Differentiability.Probability.FlatShiftAdapters
import LPP_Foundations.Model.LastPassage.Bounds
import LPP_Foundations.Shape.Uniqueness
import Martin2004.Statements.ShapeFacts
import Mathlib.Tactic

/-! Every actual upper-clipped shape is differentiable on the open quadrant.
This is the application of the main theorem in subsection `sub:ub_mom-chat` of the final draft,
with the constant-law case handled directly. -/

public section

open MeasureTheory Filter
open scoped ENNReal NNReal

namespace LPPDifferentiability.FinalDraft.Truncation

/-- The positive part of an upper-clipped weight has finite moments of
every nonnegative order. In particular, the clipped laws of subsection `sub:ub_mom-chat`
satisfy assumption (A3) at every real cutoff. -/
theorem lintegral_positivePart_rpow_upperClippedLaw_lt_top (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (M p : ℝ) (hp : 0 ≤ p) :
    (∫⁻ t, ENNReal.ofReal ((max t 0) ^ p) ∂upperClippedLaw μ M) < ∞ := by
  have hmeas : Measurable (fun t : ℝ => ENNReal.ofReal ((max t 0) ^ p)) :=
    ENNReal.measurable_ofReal.comp
      ((continuous_id.max continuous_const).rpow_const (fun _ => Or.inr hp)).measurable
  rw [upperClippedLaw, lintegral_map hmeas (by fun_prop)]
  calc
    _ ≤ ∫⁻ _ : ℝ, ENNReal.ofReal ((max M 0) ^ p) ∂μ := by
      apply lintegral_mono
      intro t
      exact ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow (le_max_right _ _) (max_le_max_right 0 (min_le_left M t)) hp)
    _ < ∞ := by
      rw [lintegral_const, measure_univ, mul_one]
      exact ENNReal.ofReal_lt_top

private theorem ae_environment_const (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (c : ℝ) (hconst : ∀ᵐ t ∂ν, t = c) :
    ∀ᵐ ω ∂environmentLaw ν, ∀ z : Lattice, ω z = c := by
  rw [ae_all_iff]
  intro z
  have hz : ∀ᵐ t ∂(environmentLaw ν).map (fun ω : Environment => ω z), t = c := by
    rwa [environmentLaw_map_eval]
  exact ae_of_ae_map (measurable_environment_eval z).aemeasurable hz

/-- For an almost-surely constant weight, the actual shape is the weight
times the length and is differentiable on the open quadrant. This covers
point-mass laws among the cutoffs in subsection `sub:ub_mom-chat`. -/
theorem const_isShapeFunction_and_differentiable (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (c : ℝ) (hconst : ∀ᵐ t ∂ν, t = c) :
    LPPStatements.IsShapeFunction ν (fun x : Quadrant => c * ((x.1 : ℝ) + x.2)) ∧
      LPPStatements.DifferentiableOnOpenQuadrant (fun x : Quadrant => c * ((x.1 : ℝ) + x.2)) := by
  constructor
  · -- The linear function has all the properties of the sample shape.
    refine ⟨by fun_prop, ?_, ?_, ?_⟩
    · intro a x
      simp only [NNReal.coe_mul]
      ring
    · intro x y a b _
      apply le_of_eq
      simp only [NNReal.coe_add, NNReal.coe_mul]
      ring
    · filter_upwards [ae_environment_const ν c hconst] with ω hω
      intro ε hε
      refine ⟨0, fun d _ => ?_⟩
      have hωeq : ω = fun _ : Lattice => c := funext hω
      have hpassage : lastPassage ω (0, 0) d = c * ((d.1 : ℝ) + d.2) := by
        rw [hωeq, lastPassage_const, Nat.cast_add, mul_comm]
      rw [hpassage]
      simp only [NNReal.coe_natCast, sub_self, abs_zero]
      positivity
  · -- Adding a multiple of the level to the zero function gives the linear shape.
    intro x hx₁ hx₂
    have hzero : DifferentiableAt ℝ (quadrantExtension (fun _ : Quadrant => (0 : ℝ))) x := by
      change DifferentiableAt ℝ (fun _ : ℝ × ℝ => (0 : ℝ)) x
      fun_prop
    simpa only [zero_add] using
      (differentiableAt_quadrantExtension_add_level_iff (fun _ : Quadrant => 0)
        c x hx₁ hx₂).mpr hzero

private theorem shape_eq {ν : Measure ℝ} [IsProbabilityMeasure ν] {g h : Quadrant → ℝ}
    (hg : LPPStatements.IsShapeFunction ν g) (hh : LPPStatements.IsShapeFunction ν h) :
    g = h :=
  shapeCandidates_eq ν g h hg.1 hh.1 hg.2.1 hh.2.1 hg.2.2.2 hh.2.2.2

/-- For every real cutoff the actual clipped law has a unique shape, and
that shape is differentiable at every point of the open quadrant. This
formalizes the application to truncated laws in subsection `sub:ub_mom-chat`. -/
theorem exists_unique_upperClipped_shape_differentiable (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hneg : LPPStatements.HasNegativePartMomentAbove μ 1)
    (M : ℝ) :
    ∃! g : Quadrant → ℝ, LPPStatements.IsShapeFunction (upperClippedLaw μ M) g ∧
      LPPStatements.DifferentiableOnOpenQuadrant g := by
  classical
  let ν := upperClippedLaw μ M
  have h : ∃ g : Quadrant → ℝ, LPPStatements.IsShapeFunction ν g ∧
      LPPStatements.DifferentiableOnOpenQuadrant g := by
    by_cases hnd : LPPStatements.NotAPointMass ν
    · -- Apply the main theorem under the inherited negative moment and bounded positive part.
      have hneg' := hasNegativePartMomentAbove_upperClippedLaw μ hneg M
      have hpos : LPPStatements.HasPositivePartMomentAbove ν 4 :=
        ⟨5, by norm_num,
          lintegral_positivePart_rpow_upperClippedLaw_lt_top μ M 5 (by norm_num)⟩
      obtain ⟨g, ⟨hc, hh, hs, ha, hd⟩, _⟩ :=
        Full.exists_unique_shape_differentiable ν hnd hneg' hpos
      exact ⟨g, ⟨hc, hh, hs, ha⟩, hd⟩
    · -- A cutoff can make the law constant. Use its exact linear shape.
      have hconst : ∃ c : ℝ, ∀ᵐ t ∂ν, t = c :=
        not_not.mp (fun hn => hnd ((LPPStatements.notAPointMass_iff_not_ae_const ν).mpr hn))
      obtain ⟨c, hc⟩ := hconst
      exact ⟨_, const_isShapeFunction_and_differentiable ν c hc⟩
  obtain ⟨g, hg, hd⟩ := h
  exact ⟨g, ⟨hg, hd⟩, fun q hq => shape_eq hq.1 hg⟩

/-- Every actual clipped shape used in subsection `sub:ub_mom-chat` is differentiable on the
open quadrant. This also applies to the shapes in the truncation comparison. -/
theorem upperClipped_shape_differentiable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : LPPStatements.HasNegativePartMomentAbove μ 1) (M : ℝ) (g : Quadrant → ℝ)
    (hg : LPPStatements.IsShapeFunction (upperClippedLaw μ M) g) :
    LPPStatements.DifferentiableOnOpenQuadrant g := by
  obtain ⟨q, ⟨hq, hd⟩, _⟩ := exists_unique_upperClipped_shape_differentiable μ hneg M
  rwa [shape_eq hg hq]

end LPPDifferentiability.FinalDraft.Truncation
