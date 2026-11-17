/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Shape.ExpectedRateShape
public import Busemann.Frozen.Definitions.SupportFacesUnion
import Busemann.Frozen.Geometry.LeftExtremeTiltExistsUnique
import Busemann.Frozen.Geometry.RightExtremeTiltExistsUnique
import Busemann.Geometry.NativeSupportGaps
import Busemann.Geometry.SupportFaceCompactness
import LPP_Foundations.Analysis.AbsoluteMomentShape

/-! # The native left endpoint of the literal two-face union -/

public section

open LPPDifferentiability MeasureTheory
open scoped NNReal ENNReal

namespace LPP.Busemann.Proof

/-- The native nonconstant moment law gives the unique left endpoint in the
interior, with all boundary gaps produced internally. This proves the approved
GRS1510.00860v2 (2.6)-(2.8) endpoint statement. -/
theorem exists_unique_left_face_endpoint
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ x, ENNReal.ofReal (|x| ^ p) ∂μ) < ∞)
    (hnonconstant : ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, x = c)
    (g : Quadrant → ℝ) (hg : IsExpectedRateShape μ g)
    (ξ : InteriorDirection) :
    ∃! left : InteriorDirection,
      ∃ hMinus hPlus : SupportTilt g,
        SupportsAt g ξ hMinus.1 ∧ SupportsAt g ξ hPlus.1 ∧
        (∀ k : SupportTilt g, SupportsAt g ξ k.1 →
          hMinus.1.1 ≤ k.1.1 ∧ k.1.1 ≤ hPlus.1.1) ∧
        left ∈ supportFacesUnion g hMinus hPlus ∧
        ∀ ζ ∈ supportFacesUnion g hMinus hPlus,
          (left.1.1 : ℝ) ≤ (ζ.1.1 : ℝ) := by
  have hgeometry := expected_rate_shape_geometry_of_absolute_moment μ g hmoment hg
  have hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z := by
    intro c z
    change g (c * z.1, c * z.2) = (c : ℝ) * g z
    exact hgeometry.2.1 c z
  have hconc : ∀ (x y : Quadrant) (r s : ℝ≥0), r + s = 1 →
      (r : ℝ) * g x + (s : ℝ) * g y ≤ g (r • x + s • y) := by
    intro x y r s hrs
    change (r : ℝ) * g x + (s : ℝ) * g y ≤
      g (r * x.1 + s * y.1, r * x.2 + s * y.2)
    exact hgeometry.2.2 x y r s hrs
  -- Use the extreme tilts, then produce their strict boundary gaps natively.
  obtain ⟨hMinus, hMinusProp, hMinusUnique⟩ :=
    LPP.Busemann.exists_unique_left_extreme_tilt g hconc hhom ξ
  obtain ⟨hPlus, hPlusProp, hPlusUnique⟩ :=
    LPP.Busemann.exists_unique_right_extreme_tilt g hconc hhom ξ
  have hMinusGaps :=
    support_tilt_strict_axis_gaps_of_absolute_moment μ hmoment hnonconstant g hg hMinus
  have hPlusGaps :=
    support_tilt_strict_axis_gaps_of_absolute_moment μ hmoment hnonconstant g hg hPlus
  have hfaces := supportFacesUnion_compact_nonempty_extrema_of_strict_axis_gaps
    g hgeometry.1 hhom hMinus hPlus
    hMinusGaps.1 hMinusGaps.2 hPlusGaps.1 hPlusGaps.2
  obtain ⟨endpoint, hEndpoint, hEndpointUnique⟩ := hfaces.2.2.1
  refine ⟨endpoint, ?_, ?_⟩
  · refine ⟨hMinus, hPlus, hMinusProp.1, hPlusProp.1, ?_, hEndpoint.1, hEndpoint.2⟩
    intro k hk
    exact ⟨hMinusProp.2 k hk, hPlusProp.2 k hk⟩
  -- A competing endpoint can carry other extreme witnesses: identify both first.
  · intro other hOther
    obtain ⟨kMinus, kPlus, hkMinus, hkPlus, hkBounds, hOtherMem, hOtherOrder⟩ := hOther
    have hMinusEq : kMinus = hMinus :=
      hMinusUnique kMinus ⟨hkMinus, fun k hk => (hkBounds k hk).1⟩
    have hPlusEq : kPlus = hPlus :=
      hPlusUnique kPlus ⟨hkPlus, fun k hk => (hkBounds k hk).2⟩
    rw [hMinusEq, hPlusEq] at hOtherMem hOtherOrder
    exact hEndpointUnique other ⟨hOtherMem, hOtherOrder⟩

end LPP.Busemann.Proof
