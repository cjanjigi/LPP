/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.Definitions.SupportTilt
public import Martin2004.Shape.ExpectedRateShape
public import LPP_Foundations.Statements.ShapeDefinitions
import Busemann.Geometry.NativeSupportGaps
import Busemann.Geometry.SupportIdentities
import LPP_Foundations.Analysis.AbsoluteMomentShape
import LPP_Foundations.Analysis.ShapeSupportingFunctionals
import Martin2004.Statements.ShapeFacts
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-! Nearby supports by the diagonal normalization in JR1810.03580v3, Lemma 4.7. -/

@[expose] public section

open Set MeasureTheory LPPDifferentiability
open scoped NNReal ENNReal Topology

namespace LPP.Busemann

private theorem exists_interior_tilted_maximizer
    (g : Quadrant → ℝ) (hg : Continuous g) (v : ℝ × ℝ)
    (ξ : InteriorDirection)
    (haxis₁ : g (1, 0) + v.1 < g ξ.1 + v.1 * (ξ.1.1 : ℝ) + v.2 * (ξ.1.2 : ℝ))
    (haxis₂ : g (0, 1) + v.2 < g ξ.1 + v.1 * (ξ.1.1 : ℝ) + v.2 * (ξ.1.2 : ℝ)) :
    ∃ η : InteriorDirection, ∀ z : Quadrant, (z.1 : ℝ) + (z.2 : ℝ) = 1 →
      g z + v.1 * (z.1 : ℝ) + v.2 * (z.2 : ℝ) ≤
        g η.1 + v.1 * (η.1.1 : ℝ) + v.2 * (η.1.2 : ℝ) := by
  let U : Set Quadrant := {z | (z.1 : ℝ) + (z.2 : ℝ) = 1}
  have hfirst : Continuous (fun z : Quadrant => (z.1 : ℝ)) :=
    NNReal.continuous_coe.comp continuous_fst
  have hsecond : Continuous (fun z : Quadrant => (z.2 : ℝ)) :=
    NNReal.continuous_coe.comp continuous_snd
  have hclosed : IsClosed U := isClosed_eq (hfirst.add hsecond) continuous_const
  have hbound : U ⊆ Icc (0 : Quadrant) (1, 1) := by
    intro z hz
    have h₁ := NNReal.coe_nonneg z.1
    have h₂ := NNReal.coe_nonneg z.2
    refine ⟨⟨zero_le, zero_le⟩, ?_, ?_⟩
    · have : (z.1 : ℝ) ≤ 1 := by change (z.1 : ℝ) + (z.2 : ℝ) = 1 at hz; linarith
      exact_mod_cast this
    · have : (z.2 : ℝ) ≤ 1 := by change (z.1 : ℝ) + (z.2 : ℝ) = 1 at hz; linarith
      exact_mod_cast this
  have hcompact : IsCompact U := isCompact_Icc.of_isClosed_subset hclosed hbound
  have hξ : ξ.1 ∈ U := ξ.2.2.2
  have hcont : Continuous (fun z : Quadrant =>
      g z + v.1 * (z.1 : ℝ) + v.2 * (z.2 : ℝ)) :=
    (hg.add (continuous_const.mul hfirst)).add (continuous_const.mul hsecond)
  obtain ⟨z, hz, hmax⟩ := hcompact.exists_isMaxOn ⟨ξ.1, hξ⟩ hcont.continuousOn
  have hsum : (z.1 : ℝ) + (z.2 : ℝ) = 1 := hz
  have hcompare := hmax hξ
  have hpos₁ : 0 < z.1 := by
    by_contra hnot
    have hz₁ : z.1 = 0 := le_antisymm (le_of_not_gt hnot) (zero_le)
    have hz₂ : z.2 = 1 := by
      have : (z.2 : ℝ) = 1 := by simpa only [hz₁, NNReal.coe_zero, zero_add] using hsum
      exact_mod_cast this
    have hzaxis : z = (0, 1) := Prod.ext hz₁ hz₂
    rw [hzaxis] at hcompare
    norm_num at hcompare
    linarith only [hcompare, haxis₂]
  have hpos₂ : 0 < z.2 := by
    by_contra hnot
    have hz₂ : z.2 = 0 := le_antisymm (le_of_not_gt hnot) (zero_le)
    have hz₁ : z.1 = 1 := by
      have : (z.1 : ℝ) = 1 := by simpa only [hz₂, NNReal.coe_zero, add_zero] using hsum
      exact_mod_cast this
    have hzaxis : z = (1, 0) := Prod.ext hz₁ hz₂
    rw [hzaxis] at hcompare
    norm_num at hcompare
    linarith only [hcompare, haxis₁]
  exact ⟨⟨z, hpos₁, hpos₂, hsum⟩, fun w hw => hmax hw⟩

private theorem normalized_maximizer_supports
    (g : Quadrant → ℝ)
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z)
    (v : ℝ × ℝ) (η : InteriorDirection)
    (hmax : ∀ z : Quadrant, (z.1 : ℝ) + (z.2 : ℝ) = 1 →
      g z + v.1 * (z.1 : ℝ) + v.2 * (z.2 : ℝ) ≤
        g η.1 + v.1 * (η.1.1 : ℝ) + v.2 * (η.1.2 : ℝ)) :
    let m := g η.1 + v.1 * (η.1.1 : ℝ) + v.2 * (η.1.2 : ℝ)
    SupportsAt g η (v.1 - m, v.2 - m) := by
  let m := g η.1 + v.1 * (η.1.1 : ℝ) + v.2 * (η.1.2 : ℝ)
  change SupportsAt g η (v.1 - m, v.2 - m)
  have hunit : ∀ z : Quadrant, (z.1 : ℝ) + (z.2 : ℝ) = 1 →
      g z ≤ (-(v.1 - m)) * (z.1 : ℝ) + (-(v.2 - m)) * (z.2 : ℝ) := by
    intro z hsum
    have h := hmax z hsum
    change g z + v.1 * (z.1 : ℝ) + v.2 * (z.2 : ℝ) ≤ m at h
    have hmul := congrArg (fun r : ℝ => m * r) hsum
    nlinarith only [h, hmul]
  have hglobal : ∀ z : Quadrant,
      g z ≤ (-(v.1 - m)) * (z.1 : ℝ) + (-(v.2 - m)) * (z.2 : ℝ) := by
    intro z
    by_cases hz : z = 0
    · subst z
      rw [quadrant_smul_homogeneous_at_zero g hhom]
      norm_num
    · let c : ℝ≥0 := z.1 + z.2
      have hc : c ≠ 0 := by
        intro hc
        have hz₁ : z.1 = 0 := (add_eq_zero.mp hc).1
        have hz₂ : z.2 = 0 := (add_eq_zero.mp hc).2
        exact hz (Prod.ext hz₁ hz₂)
      let u : Quadrant := c⁻¹ • z
      have husum : (u.1 : ℝ) + (u.2 : ℝ) = 1 := by
        change ((c⁻¹ * z.1 : ℝ≥0) : ℝ) + ((c⁻¹ * z.2 : ℝ≥0) : ℝ) = 1
        rw [← NNReal.coe_add, ← mul_add]
        change ((c⁻¹ * c : ℝ≥0) : ℝ) = 1
        rw [inv_mul_cancel₀ hc, NNReal.coe_one]
      have hscale : c • u = z := by
        dsimp only [u]
        rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
      have hcoord₁ := congrArg (fun q : Quadrant => (q.1 : ℝ)) hscale
      have hcoord₂ := congrArg (fun q : Quadrant => (q.2 : ℝ)) hscale
      change (c : ℝ) * (u.1 : ℝ) = (z.1 : ℝ) at hcoord₁
      change (c : ℝ) * (u.2 : ℝ) = (z.2 : ℝ) at hcoord₂
      calc
        g z = g (c • u) := congrArg g hscale.symm
        _ = (c : ℝ) * g u := hhom c u
        _ ≤ (c : ℝ) * ((-(v.1 - m)) * (u.1 : ℝ) + (-(v.2 - m)) * (u.2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (hunit u husum) (NNReal.coe_nonneg c)
        _ = (-(v.1 - m)) * (z.1 : ℝ) + (-(v.2 - m)) * (z.2 : ℝ) := by
          rw [← hcoord₁, ← hcoord₂]
          ring
  apply (supportsAt_iff_through_origin_majorant_and_contact g η _ hhom).mpr
  refine ⟨hglobal, ?_⟩
  have hsum := η.2.2.2
  have hmul := congrArg (fun r : ℝ => m * r) hsum
  dsimp only [m] at hmul ⊢
  nlinarith only [hmul]

/-- Under the original nonconstant absolute moment above two, every support tilt
has arbitrarily close supports on both strict sides. The construction is the
normalized first-coordinate perturbation in JR1810.03580v3, Lemma 4.7(b,d). -/
theorem exists_nearby_support_tilts_of_absolute_moment
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmoment : ∃ p : ℝ, 2 < p ∧ (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    (hμ : LPPStatements.NotAPointMass μ) (g : Quadrant → ℝ)
    (hg : IsExpectedRateShape μ g) (h : SupportTilt g) (ε : ℝ) (hε : 0 < ε) :
    ∃ a b : SupportTilt g,
      |a.1.1 - h.1.1| < ε ∧ |a.1.2 - h.1.2| < ε ∧
      |b.1.1 - h.1.1| < ε ∧ |b.1.2 - h.1.2| < ε ∧
      a.1.1 < h.1.1 ∧ h.1.1 < b.1.1 ∧ h.1.2 < a.1.2 ∧ b.1.2 < h.1.2 := by
  obtain ⟨hcont, hhom', _⟩ := expected_rate_shape_geometry_of_absolute_moment μ g hmoment hg
  have hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z := hhom'
  have hnonconstant := (LPPStatements.notAPointMass_iff_not_ae_const μ).mp hμ
  obtain ⟨hgap₁, hgap₂⟩ :=
    support_tilt_strict_axis_gaps_of_absolute_moment μ hmoment hnonconstant g hg h
  obtain ⟨ξ, hξ⟩ := h.2
  obtain ⟨hupper, hcontact⟩ :=
    (supportsAt_iff_through_origin_majorant_and_contact g ξ h.1 hhom).mp hξ
  have hξsum := ξ.2.2.2
  have hξ₁ : 0 < (ξ.1.1 : ℝ) := by exact_mod_cast ξ.2.1
  have hξ₂ : 0 < (ξ.1.2 : ℝ) := by exact_mod_cast ξ.2.2.1
  have hξ₁lt : (ξ.1.1 : ℝ) < 1 := by linarith only [hξsum, hξ₂]
  let δ := min ε (min (-h.1.1 - g (1, 0)) (-h.1.2 - g (0, 1))) / 2
  have hmargin₁ : 0 < -h.1.1 - g (1, 0) := sub_pos.mpr hgap₁
  have hmargin₂ : 0 < -h.1.2 - g (0, 1) := sub_pos.mpr hgap₂
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hδε : δ < ε := by
    have : min ε (min (-h.1.1 - g (1, 0)) (-h.1.2 - g (0, 1))) ≤ ε := min_le_left _ _
    dsimp only [δ]; linarith only [this, hε]
  have hδgap₁ : δ < -h.1.1 - g (1, 0) := by
    have hle := (min_le_right ε (min (-h.1.1 - g (1, 0)) (-h.1.2 - g (0, 1)))).trans (min_le_left _ _)
    dsimp only [δ]; linarith only [hle, hgap₁]
  have hδgap₂ : δ < -h.1.2 - g (0, 1) := by
    have hle := (min_le_right ε (min (-h.1.1 - g (1, 0)) (-h.1.2 - g (0, 1)))).trans (min_le_right _ _)
    dsimp only [δ]; linarith only [hle, hgap₂]
  have hδξpos : 0 < δ * (ξ.1.1 : ℝ) := mul_pos hδ hξ₁
  have hδξlt : δ * (ξ.1.1 : ℝ) < δ := by
    simpa only [mul_one] using mul_lt_mul_of_pos_left hξ₁lt hδ
  -- New interior contacts are chosen for the two genuinely perturbed profiles.
  obtain ⟨η, hη⟩ := exists_interior_tilted_maximizer g hcont (h.1.1 - δ, h.1.2) ξ
    (by dsimp; nlinarith only [hcontact, hgap₁, hδξlt])
    (by dsimp; nlinarith only [hcontact, hδgap₂, hδξlt])
  obtain ⟨ζ, hζ⟩ := exists_interior_tilted_maximizer g hcont (h.1.1 + δ, h.1.2) ξ
    (by dsimp; nlinarith only [hcontact, hδgap₁, hδξpos])
    (by dsimp; nlinarith only [hcontact, hgap₂, hδξpos])
  let mMinus := g η.1 + (h.1.1 - δ) * (η.1.1 : ℝ) + h.1.2 * (η.1.2 : ℝ)
  let mPlus := g ζ.1 + (h.1.1 + δ) * (ζ.1.1 : ℝ) + h.1.2 * (ζ.1.2 : ℝ)
  have hmMinusLower : -δ < mMinus := by
    have hcompare := hη ξ.1 hξsum
    dsimp only [Prod.fst, Prod.snd] at hcompare
    change g ξ.1 + (h.1.1 - δ) * (ξ.1.1 : ℝ) + h.1.2 * (ξ.1.2 : ℝ) ≤ mMinus at hcompare
    nlinarith only [hcompare, hcontact, hδξlt]
  have hmMinusUpper : mMinus < 0 := by
    have hη₁ : 0 < (η.1.1 : ℝ) := by exact_mod_cast η.2.1
    have hu := hupper η.1
    dsimp only [mMinus]
    nlinarith only [hu, hδ, hη₁]
  have hmPlusLower : 0 < mPlus := by
    have hcompare := hζ ξ.1 hξsum
    dsimp only [Prod.fst, Prod.snd] at hcompare
    change g ξ.1 + (h.1.1 + δ) * (ξ.1.1 : ℝ) + h.1.2 * (ξ.1.2 : ℝ) ≤ mPlus at hcompare
    nlinarith only [hcompare, hcontact, hδξpos]
  have hmPlusUpper : mPlus < δ := by
    have hζ₂ : 0 < (ζ.1.2 : ℝ) := by exact_mod_cast ζ.2.2.1
    have hζsum := ζ.2.2.2
    have hu := hupper ζ.1
    have hζ₁lt : (ζ.1.1 : ℝ) < 1 := by linarith only [hζsum, hζ₂]
    have hprod : δ * (ζ.1.1 : ℝ) < δ := by
      simpa only [mul_one] using mul_lt_mul_of_pos_left hζ₁lt hδ
    dsimp only [mPlus]
    nlinarith only [hu, hprod]
  let a : SupportTilt g := ⟨(h.1.1 - δ - mMinus, h.1.2 - mMinus),
    ⟨η, normalized_maximizer_supports g hhom (h.1.1 - δ, h.1.2) η hη⟩⟩
  let b : SupportTilt g := ⟨(h.1.1 + δ - mPlus, h.1.2 - mPlus),
    ⟨ζ, normalized_maximizer_supports g hhom (h.1.1 + δ, h.1.2) ζ hζ⟩⟩
  refine ⟨a, b, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change |h.1.1 - δ - mMinus - h.1.1| < ε
    rw [abs_lt]; constructor <;> linarith only [hmMinusLower, hmMinusUpper, hδε]
  · change |h.1.2 - mMinus - h.1.2| < ε
    rw [abs_lt]; constructor <;> linarith only [hmMinusLower, hmMinusUpper, hδε]
  · change |h.1.1 + δ - mPlus - h.1.1| < ε
    rw [abs_lt]; constructor <;> linarith only [hmPlusLower, hmPlusUpper, hδε]
  · change |h.1.2 - mPlus - h.1.2| < ε
    rw [abs_lt]; constructor <;> linarith only [hmPlusLower, hmPlusUpper, hδε]
  · change h.1.1 - δ - mMinus < h.1.1
    linarith only [hmMinusLower]
  · change h.1.1 < h.1.1 + δ - mPlus
    linarith only [hmPlusUpper]
  · change h.1.2 < h.1.2 - mMinus
    linarith only [hmMinusUpper]
  · change h.1.2 - mPlus < h.1.2
    linarith only [hmPlusLower]

end LPP.Busemann
