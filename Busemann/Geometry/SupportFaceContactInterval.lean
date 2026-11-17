/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Geometry.SupportFaceCompactness
public import Busemann.Geometry.SupportFaceIntervals
import Busemann.Geometry.SupportIdentities
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # The contact interval for one support face -/

@[expose] public section

open LPPDifferentiability
open scoped NNReal

namespace LPP.Busemann

/-- A single support face has actual first-coordinate endpoints, and its
contact condition on the closed simplex is exactly the interval between them.
This is the finite contact geometry used in GRS arXiv:1510.00860v2, (2.6)–(2.8). -/
theorem exists_support_face_interval_with_contact_characterization
    (g : Quadrant → ℝ) (hgcont : Continuous g)
    (hconc : ∀ (x y : Quadrant) (a b : ℝ≥0), a + b = 1 →
      (a : ℝ) * g x + (b : ℝ) * g y ≤ g (a • x + b • y))
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z)
    (h : SupportTilt g)
    (hgap₁ : g (1, 0) < -h.1.1) (hgap₂ : g (0, 1) < -h.1.2) :
    ∃ left right : InteriorDirection,
      left ∈ supportFace g h ∧ right ∈ supportFace g h ∧
      (∀ ζ ∈ supportFace g h, (left.1.1 : ℝ) ≤ (ζ.1.1 : ℝ)) ∧
      (∀ ζ ∈ supportFace g h, (ζ.1.1 : ℝ) ≤ (right.1.1 : ℝ)) ∧
      let q : ℝ → Quadrant := fun t =>
        (Real.toNNReal t, Real.toNNReal (1 - t))
      ∀ t : ℝ, t ∈ Set.Icc 0 1 →
        (g (q t) + h.1.1 * t + h.1.2 * (1 - t) = 0 ↔
          (left.1.1 : ℝ) ≤ t ∧ t ≤ (right.1.1 : ℝ)) := by
  obtain ⟨ξ, hξ⟩ := h.2
  have hmajorant : ∀ z : Quadrant,
      g z ≤ (-h.1.1) * (z.1 : ℝ) + (-h.1.2) * (z.2 : ℝ) :=
    ((supportsAt_iff_through_origin_majorant_and_contact g ξ h.1 hhom).mp hξ).1
  -- Reuse the compact two-face extremum theorem with equal tilts.
  have hfaces := supportFacesUnion_compact_nonempty_extrema_of_strict_axis_gaps
    g hgcont hhom h h hgap₁ hgap₂ hgap₁ hgap₂
  have hleftUnique : ∃! η : InteriorDirection,
      η ∈ supportFace g h ∧
        ∀ ζ ∈ supportFace g h, (η.1.1 : ℝ) ≤ (ζ.1.1 : ℝ) := by
    simpa [supportFacesUnion] using hfaces.2.2.1
  have hrightUnique : ∃! η : InteriorDirection,
      η ∈ supportFace g h ∧
        ∀ ζ ∈ supportFace g h, (ζ.1.1 : ℝ) ≤ (η.1.1 : ℝ) := by
    simpa [supportFacesUnion] using hfaces.2.2.2
  obtain ⟨left, hleftProp, _⟩ := hleftUnique
  obtain ⟨hleftMem, hleftMin⟩ := hleftProp
  obtain ⟨right, hrightProp, _⟩ := hrightUnique
  obtain ⟨hrightMem, hrightMax⟩ := hrightProp
  have hleftFirstPos : (0 : ℝ) < (left.1.1 : ℝ) :=
    NNReal.coe_pos.2 left.2.1
  have hleftSecondPos : (0 : ℝ) < (left.1.2 : ℝ) :=
    NNReal.coe_pos.2 left.2.2.1
  have hleftFirstLtOne : (left.1.1 : ℝ) < 1 := by
    have hsum := left.2.2.2
    linarith
  have hrightFirstPos : (0 : ℝ) < (right.1.1 : ℝ) :=
    NNReal.coe_pos.2 right.2.1
  have hrightSecondPos : (0 : ℝ) < (right.1.2 : ℝ) :=
    NNReal.coe_pos.2 right.2.2.1
  have hrightFirstLtOne : (right.1.1 : ℝ) < 1 := by
    have hsum := right.2.2.2
    linarith
  refine ⟨left, right, hleftMem, hrightMem, hleftMin, hrightMax, ?_⟩
  dsimp only
  intro t ht
  by_cases ht0 : t = 0
  · subst t
    have hgapZeroNegative : g (0, 1) + h.1.2 < 0 := by
      linarith [hgap₂]
    constructor
    · intro hzero
      have hzero' : g (0, 1) + h.1.2 = 0 := by
        simpa using hzero
      linarith
    · rintro ⟨hleftZero, _⟩
      linarith
  · by_cases ht1 : t = 1
    · subst t
      have hgapOneNegative : g (1, 0) + h.1.1 < 0 := by
        linarith [hgap₁]
      constructor
      · intro hzero
        have hzero' : g (1, 0) + h.1.1 = 0 := by
          simpa using hzero
        linarith
      · rintro ⟨_, hrightOne⟩
        linarith
    · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      have htlt : t < 1 := lt_of_le_of_ne ht.2 ht1
      have hsecondPos : 0 < 1 - t := sub_pos.mpr htlt
      have hsecondNonneg : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
      let η : InteriorDirection :=
        ⟨(Real.toNNReal t, Real.toNNReal (1 - t)),
          ⟨Real.toNNReal_pos.mpr htpos,
            Real.toNNReal_pos.mpr hsecondPos, by
              rw [Real.coe_toNNReal t ht.1,
                Real.coe_toNNReal (1 - t) hsecondNonneg]
              ring⟩⟩
      have hηFirst : (η.1.1 : ℝ) = t := Real.coe_toNNReal t ht.1
      have hηSecond : (η.1.2 : ℝ) = 1 - t :=
        Real.coe_toNNReal (1 - t) hsecondNonneg
      have hηValue : η.1 = (Real.toNNReal t, Real.toNNReal (1 - t)) := rfl
      have hfaceContact : η ∈ supportFace g h ↔
          g η.1 + h.1.1 * (η.1.1 : ℝ) + h.1.2 * (η.1.2 : ℝ) = 0 := by
        change SupportsAt g η h.1 ↔ _
        rw [supportsAt_iff_through_origin_majorant_and_contact g η h.1 hhom]
        constructor
        · rintro ⟨_, hcontact⟩
          linarith
        · intro hzero
          refine ⟨hmajorant, ?_⟩
          linarith
      have hgapIffFace :
          g (Real.toNNReal t, Real.toNNReal (1 - t)) +
            h.1.1 * t + h.1.2 * (1 - t) = 0 ↔ η ∈ supportFace g h := by
        rw [hfaceContact, hηFirst, hηSecond, hηValue]
      change
        (g (Real.toNNReal t, Real.toNNReal (1 - t)) +
          h.1.1 * t + h.1.2 * (1 - t) = 0) ↔
        ((left.1.1 : ℝ) ≤ t ∧ t ≤ (right.1.1 : ℝ))
      rw [hgapIffFace]
      constructor
      · intro hηFace
        have hleftBound := hleftMin η hηFace
        have hrightBound := hrightMax η hηFace
        rw [hηFirst] at hleftBound hrightBound
        exact ⟨hleftBound, hrightBound⟩
      · rintro ⟨hleftT, htright⟩
        have hleftη : left.1.1 ≤ η.1.1 := by
          apply NNReal.coe_le_coe.1
          rw [hηFirst]
          exact hleftT
        have hηright : η.1.1 ≤ right.1.1 := by
          apply NNReal.coe_le_coe.1
          rw [hηFirst]
          exact htright
        exact supportFace_mem_of_between g hconc hhom h left right η
          hleftMem hrightMem hleftη hηright

end LPP.Busemann
