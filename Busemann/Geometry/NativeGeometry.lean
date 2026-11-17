/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.Definitions.SupportFacesUnion
public import Martin2004.Shape.ExpectedRateShape
public import Martin2004.Statements.ShapeFacts
import Busemann.Frozen.Geometry.LeftExtremeTiltExistsUnique
import Busemann.Frozen.Geometry.RightExtremeTiltExistsUnique
import Busemann.Frozen.Geometry.LeftFaceEndpointExistsUnique
import Busemann.Frozen.Geometry.RightFaceEndpointExistsUnique
import Busemann.Geometry.SupportFaceIntervals
import LPP_Foundations.Analysis.AbsoluteMomentShape

/-!
# Native extreme supports and endpoints

This module selects the unique extreme supports and the endpoints of their
literal two-face union under the original native law. The selection combines
JR arXiv:1810.03580v3, Section 2.3 and Lemma 4.7(c), with GRS
arXiv:1510.00860v2, (2.6)–(2.8). It does not address endpoint passage limits.
-/

@[expose] public section

open LPPDifferentiability MeasureTheory
open scoped NNReal ENNReal

namespace LPP.Busemann

/-- Select the native extreme supports and the interior endpoints of the
literal union of their faces. The four unique-existence theorems identify the
chosen objects; `supportFacesUnion_mem_iff_between_extrema` gives the interval. -/
theorem exists_native_extreme_tilts_and_face_endpoints
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.NotAPointMass μ)
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    (g : Quadrant → ℝ) (hg : IsExpectedRateShape μ g) :
    ∃ (hL hR : InteriorDirection → SupportTilt g)
      (leftEndpoint rightEndpoint : InteriorDirection → InteriorDirection),
      (∀ ξ : InteriorDirection,
        SupportsAt g ξ (hL ξ).1 ∧ SupportsAt g ξ (hR ξ).1 ∧
        ∀ h : SupportTilt g, SupportsAt g ξ h.1 →
          (hL ξ).1.1 ≤ h.1.1 ∧ h.1.1 ≤ (hR ξ).1.1) ∧
      (∀ ξ η : InteriorDirection,
        η ∈ supportFacesUnion g (hL ξ) (hR ξ) ↔
          (leftEndpoint ξ).1.1 ≤ η.1.1 ∧
            η.1.1 ≤ (rightEndpoint ξ).1.1) := by
  obtain ⟨_, hhom', hconc'⟩ :=
    expected_rate_shape_geometry_of_absolute_moment μ g hmoment hg
  have hhom : ∀ (c : ℝ≥0) (z : Quadrant),
      g (c • z) = (c : ℝ) * g z := hhom'
  have hconc : ∀ (x y : Quadrant) (a b : ℝ≥0), a + b = 1 →
      (a : ℝ) * g x + (b : ℝ) * g y ≤ g (a • x + b • y) := hconc'
  have hnonconstant : ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, x = c :=
    (LPPStatements.notAPointMass_iff_not_ae_const μ).mp hμ
  let hL : InteriorDirection → SupportTilt g := fun ξ =>
    Classical.choose (exists_unique_left_extreme_tilt g hconc hhom ξ).exists
  let hR : InteriorDirection → SupportTilt g := fun ξ =>
    Classical.choose (exists_unique_right_extreme_tilt g hconc hhom ξ).exists
  let leftEndpoint : InteriorDirection → InteriorDirection := fun ξ =>
    Classical.choose
      (exists_unique_left_face_endpoint μ hmoment hnonconstant g hg ξ).exists
  let rightEndpoint : InteriorDirection → InteriorDirection := fun ξ =>
    Classical.choose
      (exists_unique_right_face_endpoint μ hmoment hnonconstant g hg ξ).exists
  have hLspec (ξ : InteriorDirection) :
      SupportsAt g ξ (hL ξ).1 ∧
        ∀ k : SupportTilt g, SupportsAt g ξ k.1 → (hL ξ).1.1 ≤ k.1.1 :=
    Classical.choose_spec
      (exists_unique_left_extreme_tilt g hconc hhom ξ).exists
  have hRspec (ξ : InteriorDirection) :
      SupportsAt g ξ (hR ξ).1 ∧
        ∀ k : SupportTilt g, SupportsAt g ξ k.1 → k.1.1 ≤ (hR ξ).1.1 :=
    Classical.choose_spec
      (exists_unique_right_extreme_tilt g hconc hhom ξ).exists
  have hLeftSpec (ξ : InteriorDirection) :
      ∃ hMinus hPlus : SupportTilt g,
        SupportsAt g ξ hMinus.1 ∧ SupportsAt g ξ hPlus.1 ∧
        (∀ k : SupportTilt g, SupportsAt g ξ k.1 →
          hMinus.1.1 ≤ k.1.1 ∧ k.1.1 ≤ hPlus.1.1) ∧
        leftEndpoint ξ ∈ supportFacesUnion g hMinus hPlus ∧
        ∀ ζ ∈ supportFacesUnion g hMinus hPlus,
          (leftEndpoint ξ).1.1 ≤ (ζ.1.1 : ℝ) :=
    Classical.choose_spec
      (exists_unique_left_face_endpoint μ hmoment hnonconstant g hg ξ).exists
  have hRightSpec (ξ : InteriorDirection) :
      ∃ hMinus hPlus : SupportTilt g,
        SupportsAt g ξ hMinus.1 ∧ SupportsAt g ξ hPlus.1 ∧
        (∀ k : SupportTilt g, SupportsAt g ξ k.1 →
          hMinus.1.1 ≤ k.1.1 ∧ k.1.1 ≤ hPlus.1.1) ∧
        rightEndpoint ξ ∈ supportFacesUnion g hMinus hPlus ∧
        ∀ ζ ∈ supportFacesUnion g hMinus hPlus,
          (ζ.1.1 : ℝ) ≤ (rightEndpoint ξ).1.1 :=
    Classical.choose_spec
      (exists_unique_right_face_endpoint μ hmoment hnonconstant g hg ξ).exists
  have hLeft (ξ : InteriorDirection) :
      leftEndpoint ξ ∈ supportFacesUnion g (hL ξ) (hR ξ) ∧
      ∀ ζ ∈ supportFacesUnion g (hL ξ) (hR ξ),
        (leftEndpoint ξ).1.1 ≤ (ζ.1.1 : ℝ) := by
    obtain ⟨hMinus, hPlus, hMinusSupport, hPlusSupport, horder,
      hmem, hmin⟩ := hLeftSpec ξ
    have hMinusEq : hMinus = hL ξ :=
      (exists_unique_left_extreme_tilt g hconc hhom ξ).unique
        ⟨hMinusSupport, fun k hk => (horder k hk).1⟩ (hLspec ξ)
    have hPlusEq : hPlus = hR ξ :=
      (exists_unique_right_extreme_tilt g hconc hhom ξ).unique
        ⟨hPlusSupport, fun k hk => (horder k hk).2⟩ (hRspec ξ)
    rw [hMinusEq, hPlusEq] at hmem hmin
    exact ⟨hmem, hmin⟩
  have hRight (ξ : InteriorDirection) :
      rightEndpoint ξ ∈ supportFacesUnion g (hL ξ) (hR ξ) ∧
      ∀ ζ ∈ supportFacesUnion g (hL ξ) (hR ξ),
        (ζ.1.1 : ℝ) ≤ (rightEndpoint ξ).1.1 := by
    obtain ⟨hMinus, hPlus, hMinusSupport, hPlusSupport, horder,
      hmem, hmax⟩ := hRightSpec ξ
    have hMinusEq : hMinus = hL ξ :=
      (exists_unique_left_extreme_tilt g hconc hhom ξ).unique
        ⟨hMinusSupport, fun k hk => (horder k hk).1⟩ (hLspec ξ)
    have hPlusEq : hPlus = hR ξ :=
      (exists_unique_right_extreme_tilt g hconc hhom ξ).unique
        ⟨hPlusSupport, fun k hk => (horder k hk).2⟩ (hRspec ξ)
    rw [hMinusEq, hPlusEq] at hmem hmax
    exact ⟨hmem, hmax⟩
  refine ⟨hL, hR, leftEndpoint, rightEndpoint, ?_, ?_⟩
  · intro ξ
    exact ⟨(hLspec ξ).1, (hRspec ξ).1,
      fun h hh => ⟨(hLspec ξ).2 h hh, (hRspec ξ).2 h hh⟩⟩
  · intro ξ η
    have hreal := supportFacesUnion_mem_iff_between_extrema g hconc hhom
      (hL ξ) (hR ξ) ξ (leftEndpoint ξ) (rightEndpoint ξ)
      (hLspec ξ).1 (hRspec ξ).1
      (hLeft ξ).1 (hRight ξ).1 (hLeft ξ).2 (hRight ξ).2 η
    constructor
    · intro hmem
      rcases hreal.mp hmem with ⟨hlo, hhi⟩
      exact ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩
    · rintro ⟨hlo, hhi⟩
      apply hreal.mpr
      exact ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩

end LPP.Busemann
