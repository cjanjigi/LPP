/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.Definitions.SupportFacesUnion
import Busemann.Geometry.SupportIdentities
import Mathlib.Analysis.Convex.NNReal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Contact intervals for the literal union of two supporting faces. -/

@[expose] public section

open LPPDifferentiability
open scoped NNReal

namespace LPP.Busemann

/-- A support face contains each interior direction between two of its points, as in
GRS arXiv:1510.00860v2, (2.6). -/
theorem supportFace_mem_of_between
    (g : Quadrant → ℝ)
    (hconc : ∀ (x y : Quadrant) (a b : ℝ≥0), a + b = 1 →
      (a : ℝ) * g x + (b : ℝ) * g y ≤ g (a • x + b • y))
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z)
    (h : SupportTilt g) (u v η : InteriorDirection)
    (hu : u ∈ supportFace g h) (hv : v ∈ supportFace g h)
    (huη : u.1.1 ≤ η.1.1) (hηv : η.1.1 ≤ v.1.1) :
    η ∈ supportFace g h := by
  have hsegment := NNReal.Icc_subset_segment (show η.1.1 ∈ Set.Icc u.1.1 v.1.1 from ⟨huη, hηv⟩)
  obtain ⟨a, b, -, -, hab, hfirst⟩ := hsegment
  have hfirst' : a * u.1.1 + b * v.1.1 = η.1.1 := by
    simpa only [smul_eq_mul] using hfirst
  have hsecond : a * u.1.2 + b * v.1.2 = η.1.2 := by
    apply NNReal.coe_injective
    have hab' : (a : ℝ) + (b : ℝ) = 1 := by exact_mod_cast hab
    have hfirstReal : (a : ℝ) * (u.1.1 : ℝ) + (b : ℝ) * (v.1.1 : ℝ) =
        (η.1.1 : ℝ) := by exact_mod_cast hfirst'
    have hau : (a : ℝ) * ((u.1.1 : ℝ) + (u.1.2 : ℝ)) = (a : ℝ) := by
      rw [u.2.2.2]; ring
    have hbv : (b : ℝ) * ((v.1.1 : ℝ) + (v.1.2 : ℝ)) = (b : ℝ) := by
      rw [v.2.2.2]; ring
    simp only [NNReal.coe_add, NNReal.coe_mul]
    nlinarith only [hab', hfirstReal, hau, hbv, η.2.2.2]
  have hpoint : a • u.1 + b • v.1 = η.1 := by
    apply Prod.ext
    · exact hfirst'
    · exact hsecond
  have hsupportU : SupportsAt g u h.1 := hu
  have hsupportV : SupportsAt g v h.1 := hv
  obtain ⟨hupper, hcontactU⟩ :=
    (supportsAt_iff_through_origin_majorant_and_contact g u h.1 hhom).1 hsupportU
  have hcontactV :=
    ((supportsAt_iff_through_origin_majorant_and_contact g v h.1 hhom).1 hsupportV).2
  have hlower := hconc u.1 v.1 a b hab
  rw [hpoint, hcontactU, hcontactV] at hlower
  have hlinear : (a : ℝ) * ((-h.1.1) * (u.1.1 : ℝ) + (-h.1.2) * (u.1.2 : ℝ)) +
      (b : ℝ) * ((-h.1.1) * (v.1.1 : ℝ) + (-h.1.2) * (v.1.2 : ℝ)) =
      (-h.1.1) * (η.1.1 : ℝ) + (-h.1.2) * (η.1.2 : ℝ) := by
    rw [← hfirst', ← hsecond]
    simp only [NNReal.coe_add, NNReal.coe_mul]
    ring
  rw [hlinear] at hlower
  exact (supportsAt_iff_through_origin_majorant_and_contact g η h.1 hhom).2
    ⟨hupper, le_antisymm (hupper η.1) hlower⟩

/-- The literal union of two faces meeting at ξ is exactly the interval between its
actual first-coordinate extrema, as in GRS arXiv:1510.00860v2, (2.6)–(2.8). -/
theorem supportFacesUnion_mem_iff_between_extrema
    (g : Quadrant → ℝ)
    (hconc : ∀ (x y : Quadrant) (a b : ℝ≥0), a + b = 1 →
      (a : ℝ) * g x + (b : ℝ) * g y ≤ g (a • x + b • y))
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z)
    (hMinus hPlus : SupportTilt g) (ξ left right : InteriorDirection)
    (hξMinus : SupportsAt g ξ hMinus.1) (hξPlus : SupportsAt g ξ hPlus.1)
    (hleft : left ∈ supportFacesUnion g hMinus hPlus)
    (hright : right ∈ supportFacesUnion g hMinus hPlus)
    (hmin : ∀ ζ ∈ supportFacesUnion g hMinus hPlus, (left.1.1 : ℝ) ≤ (ζ.1.1 : ℝ))
    (hmax : ∀ ζ ∈ supportFacesUnion g hMinus hPlus, (ζ.1.1 : ℝ) ≤ (right.1.1 : ℝ))
    (η : InteriorDirection) :
    η ∈ supportFacesUnion g hMinus hPlus ↔
      (left.1.1 : ℝ) ≤ (η.1.1 : ℝ) ∧ (η.1.1 : ℝ) ≤ (right.1.1 : ℝ) := by
  constructor
  · intro hη
    exact ⟨hmin η hη, hmax η hη⟩
  · rintro ⟨hleftη, hηright⟩
    rcases le_total (η.1.1 : ℝ) (ξ.1.1 : ℝ) with hηξ | hξη
    · have hleftη' : left.1.1 ≤ η.1.1 := by exact_mod_cast hleftη
      have hηξ' : η.1.1 ≤ ξ.1.1 := by exact_mod_cast hηξ
      rcases hleft with hleft | hleft
      · exact Or.inl (supportFace_mem_of_between g hconc hhom hMinus left ξ η
          hleft hξMinus hleftη' hηξ')
      · exact Or.inr (supportFace_mem_of_between g hconc hhom hPlus left ξ η
          hleft hξPlus hleftη' hηξ')
    · have hξη' : ξ.1.1 ≤ η.1.1 := by exact_mod_cast hξη
      have hηright' : η.1.1 ≤ right.1.1 := by exact_mod_cast hηright
      rcases hright with hright | hright
      · exact Or.inl (supportFace_mem_of_between g hconc hhom hMinus ξ right η
          hξMinus hright hξη' hηright')
      · exact Or.inr (supportFace_mem_of_between g hconc hhom hPlus ξ right η
          hξPlus hright hξη' hηright')

end LPP.Busemann
