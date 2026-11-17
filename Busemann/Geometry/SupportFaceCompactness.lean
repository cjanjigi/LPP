/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.Definitions.SupportFacesUnion
public import Mathlib.Topology.Order.Compact
import Busemann.Geometry.SupportIdentities
import Mathlib.Tactic.Linarith

/-!
# Compact support faces away from the axes

Strict axis gaps keep the closed unit-sum contact set in the interior. The
actual two-face union is then compact and has unique coordinate extrema.
-/

public section

open Set LPPDifferentiability
open scoped NNReal

namespace LPP.Busemann

private theorem interiorDirection_eq_of_first_coord_eq
    (ξ η : InteriorDirection) (hfirst : (ξ.1.1 : ℝ) = (η.1.1 : ℝ)) : ξ = η := by
  apply Subtype.ext
  apply Prod.ext
  · exact NNReal.coe_injective hfirst
  · apply NNReal.coe_injective
    linarith only [ξ.2.2.2, η.2.2.2, hfirst]

/-- Strict gaps at both axes make the actual interior support face compact.
This is the conditional compactness step for the face endpoints in
GRS1510.00860v2, equations (2.6)-(2.8); boundary estimates must supply the gaps. -/
theorem isCompact_supportFace_of_strict_axis_gaps
    (g : Quadrant → ℝ) (hgcont : Continuous g)
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z)
    (h : SupportTilt g)
    (hgap₁ : g (1, 0) < -h.1.1) (hgap₂ : g (0, 1) < -h.1.2) :
    IsCompact (supportFace g h) := by
  let K : Set Quadrant := {z | (z.1 : ℝ) + (z.2 : ℝ) = 1 ∧
    g z = (-h.1.1) * (z.1 : ℝ) + (-h.1.2) * (z.2 : ℝ)}
  have hfirst : Continuous (fun z : Quadrant => (z.1 : ℝ)) :=
    NNReal.continuous_coe.comp continuous_fst
  have hsecond : Continuous (fun z : Quadrant => (z.2 : ℝ)) :=
    NNReal.continuous_coe.comp continuous_snd
  -- The contact set is closed and bounded inside the closed quadrant simplex.
  have hKclosed : IsClosed K :=
    (isClosed_eq (hfirst.add hsecond) continuous_const).inter
      (isClosed_eq hgcont ((continuous_const.mul hfirst).add
        (continuous_const.mul hsecond)))
  have hKbound : K ⊆ Icc (0 : Quadrant) (1, 1) := by
    intro z hz
    have h₁ : 0 ≤ (z.1 : ℝ) := NNReal.coe_nonneg _
    have h₂ : 0 ≤ (z.2 : ℝ) := NNReal.coe_nonneg _
    constructor
    · exact ⟨zero_le, zero_le⟩
    · constructor
      · have hle : (z.1 : ℝ) ≤ 1 := by linarith only [hz.1, h₂]
        exact_mod_cast hle
      · have hle : (z.2 : ℝ) ≤ 1 := by linarith only [hz.1, h₁]
        exact_mod_cast hle
  have hbox : IsCompact (Icc (0 : Quadrant) (1, 1)) := isCompact_Icc
  have hKcompact : IsCompact K := hbox.of_isClosed_subset hKclosed hKbound
  -- Either zero coordinate would force contact at an axis, contrary to its gap.
  have hKinterior : ∀ z ∈ K, 0 < z.1 ∧ 0 < z.2 := by
    intro z hz
    have hnonzero₁ : z.1 ≠ 0 := by
      intro hz₁
      have hz₂ : z.2 = 1 := by
        have hsum := hz.1
        rw [hz₁, NNReal.coe_zero, zero_add] at hsum
        exact_mod_cast hsum
      have hzaxis : z = (0, 1) := Prod.ext hz₁ hz₂
      have hcontact := hz.2
      rw [hzaxis] at hcontact
      norm_num at hcontact
      exact (ne_of_lt hgap₂) hcontact
    have hnonzero₂ : z.2 ≠ 0 := by
      intro hz₂
      have hz₁ : z.1 = 1 := by
        have hsum := hz.1
        rw [hz₂, NNReal.coe_zero, add_zero] at hsum
        exact_mod_cast hsum
      have hzaxis : z = (1, 0) := Prod.ext hz₁ hz₂
      have hcontact := hz.2
      rw [hzaxis] at hcontact
      norm_num at hcontact
      exact (ne_of_lt hgap₁) hcontact
    exact ⟨lt_of_le_of_ne (zero_le) (Ne.symm hnonzero₁),
      lt_of_le_of_ne (zero_le) (Ne.symm hnonzero₂)⟩
  obtain ⟨ξ, hξ⟩ := h.2
  have hmajorant :=
    ((supportsAt_iff_through_origin_majorant_and_contact g ξ h.1 hhom).mp hξ).1
  -- Euler contact identifies the actual face image with this closed contact set.
  have himage : (Subtype.val : InteriorDirection → Quadrant) '' supportFace g h = K := by
    ext z
    constructor
    · rintro ⟨η, hη, rfl⟩
      exact ⟨η.2.2.2,
        ((supportsAt_iff_through_origin_majorant_and_contact g η h.1 hhom).mp hη).2⟩
    · intro hz
      let η : InteriorDirection := ⟨z, (hKinterior z hz).1, (hKinterior z hz).2, hz.1⟩
      refine ⟨η, ?_, rfl⟩
      exact (supportsAt_iff_through_origin_majorant_and_contact g η h.1 hhom).mpr
        ⟨hmajorant, hz.2⟩
  apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
  rw [himage]
  exact hKcompact

/-- With strict axis gaps for both tilts, their literal two-face union is
compact and nonempty and has unique first-coordinate minimum and maximum.
These are conditional endpoint prerequisites for GRS1510.00860v2 (2.6)-(2.8).
No convexity or assertion that the union is one affine piece is needed. -/
theorem supportFacesUnion_compact_nonempty_extrema_of_strict_axis_gaps
    (g : Quadrant → ℝ) (hgcont : Continuous g)
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z)
    (hMinus hPlus : SupportTilt g)
    (hMinusGap₁ : g (1, 0) < -hMinus.1.1) (hMinusGap₂ : g (0, 1) < -hMinus.1.2)
    (hPlusGap₁ : g (1, 0) < -hPlus.1.1) (hPlusGap₂ : g (0, 1) < -hPlus.1.2) :
    IsCompact (supportFacesUnion g hMinus hPlus) ∧
      (supportFacesUnion g hMinus hPlus).Nonempty ∧
      (∃! ξ : InteriorDirection, ξ ∈ supportFacesUnion g hMinus hPlus ∧
        ∀ η ∈ supportFacesUnion g hMinus hPlus, (ξ.1.1 : ℝ) ≤ (η.1.1 : ℝ)) ∧
      (∃! ξ : InteriorDirection, ξ ∈ supportFacesUnion g hMinus hPlus ∧
        ∀ η ∈ supportFacesUnion g hMinus hPlus, (η.1.1 : ℝ) ≤ (ξ.1.1 : ℝ)) := by
  let U : Set InteriorDirection := supportFacesUnion g hMinus hPlus
  change IsCompact U ∧ U.Nonempty ∧
    (∃! ξ : InteriorDirection, ξ ∈ U ∧ ∀ η ∈ U, (ξ.1.1 : ℝ) ≤ (η.1.1 : ℝ)) ∧
    (∃! ξ : InteriorDirection, ξ ∈ U ∧ ∀ η ∈ U, (η.1.1 : ℝ) ≤ (ξ.1.1 : ℝ))
  have hcompact : IsCompact U :=
    (isCompact_supportFace_of_strict_axis_gaps g hgcont hhom hMinus
      hMinusGap₁ hMinusGap₂).union
      (isCompact_supportFace_of_strict_axis_gaps g hgcont hhom hPlus hPlusGap₁ hPlusGap₂)
  have hnonempty : U.Nonempty := by
    obtain ⟨ξ, hξ⟩ := hMinus.2
    exact ⟨ξ, Or.inl hξ⟩
  have hcoord : Continuous (fun ξ : InteriorDirection => (ξ.1.1 : ℝ)) :=
    NNReal.continuous_coe.comp (continuous_fst.comp continuous_subtype_val)
  refine ⟨hcompact, hnonempty, ?_, ?_⟩
  -- Compactness gives attained extrema; unit sum makes the first coordinate injective.
  · obtain ⟨ξ, hξ, hmin⟩ := hcompact.exists_isMinOn hnonempty hcoord.continuousOn
    refine ⟨ξ, ⟨hξ, hmin⟩, ?_⟩
    intro η hη
    apply interiorDirection_eq_of_first_coord_eq
    exact le_antisymm (hη.2 ξ hξ) (hmin hη.1)
  · obtain ⟨ξ, hξ, hmax⟩ := hcompact.exists_isMaxOn hnonempty hcoord.continuousOn
    refine ⟨ξ, ⟨hξ, hmax⟩, ?_⟩
    intro η hη
    apply interiorDirection_eq_of_first_coord_eq
    exact le_antisymm (hmax hη.1) (hη.2 ξ hξ)

end LPP.Busemann
