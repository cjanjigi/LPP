/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.Definitions.SupportTilt
import Busemann.Geometry.SupportIdentities
import Mathlib.Tactic.Linarith

/-!
# Coordinate order for homogeneous support tilts

The support majorants order the coordinates of any two actual
interior-contact tilts.
-/

@[expose] public section

open LPPDifferentiability
open scoped NNReal

namespace LPP.Busemann

/-- Actual homogeneous support tilts have opposite second-coordinate order,
and a first coordinate determines the whole tilt. The majorant/contact
characterization is the support inequality from JR arXiv:1810.03580v3, (2.5). -/
theorem supportTilt_coordinate_order
    (g : Quadrant → ℝ)
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z)
    (h k : SupportTilt g) :
    (h.1.1 < k.1.1 →
      k.1.2 < h.1.2 ∧ h.1.1 - h.1.2 < k.1.1 - k.1.2) ∧
    (h.1.1 = k.1.1 → h = k) := by
  rcases h.2 with ⟨ξh, hsupph⟩
  rcases k.2 with ⟨ξk, hsuppk⟩
  have hdata :=
    (supportsAt_iff_through_origin_majorant_and_contact g ξh h.1 hhom).mp hsupph
  have kdata :=
    (supportsAt_iff_through_origin_majorant_and_contact g ξk k.1 hhom).mp hsuppk
  have hxH : 0 < (ξh.1.1 : ℝ) := by exact_mod_cast ξh.2.1
  have hyH : 0 < (ξh.1.2 : ℝ) := by exact_mod_cast ξh.2.2.1
  have hyK : 0 < (ξk.1.2 : ℝ) := by exact_mod_cast ξk.2.2.1
  have hcrossK : 0 ≤
      (k.1.1 - h.1.1) * (ξk.1.1 : ℝ) +
        (k.1.2 - h.1.2) * (ξk.1.2 : ℝ) := by
    have hbound := hdata.1 ξk.1
    rw [kdata.2] at hbound
    linarith
  have hcrossH :
      (k.1.1 - h.1.1) * (ξh.1.1 : ℝ) +
        (k.1.2 - h.1.2) * (ξh.1.2 : ℝ) ≤ 0 := by
    have hbound := kdata.1 ξh.1
    rw [hdata.2] at hbound
    linarith
  refine ⟨?_, ?_⟩
  · intro hfirst
    have hfirstPositive :
        0 < (k.1.1 - h.1.1) * (ξh.1.1 : ℝ) :=
      mul_pos (sub_pos.mpr hfirst) hxH
    have hsecond : k.1.2 < h.1.2 := by
      by_contra hnot
      have hle : h.1.2 ≤ k.1.2 := le_of_not_gt hnot
      have hsecondNonnegative :
          0 ≤ (k.1.2 - h.1.2) * (ξh.1.2 : ℝ) :=
        mul_nonneg (sub_nonneg.mpr hle) (le_of_lt hyH)
      linarith [hcrossH, hfirstPositive, hsecondNonnegative]
    exact ⟨hsecond, by linarith⟩
  · intro hfirst
    have hsecondNonnegative : 0 ≤ k.1.2 - h.1.2 := by
      by_contra hnot
      have hsecondNegative : k.1.2 - h.1.2 < 0 := lt_of_not_ge hnot
      have hproductNegative :
          (k.1.2 - h.1.2) * (ξk.1.2 : ℝ) < 0 :=
        mul_neg_of_neg_of_pos hsecondNegative hyK
      rw [hfirst] at hcrossK
      linarith [hcrossK, hproductNegative]
    have hsecondNonpositive : k.1.2 - h.1.2 ≤ 0 := by
      by_contra hnot
      have hsecondPositive : 0 < k.1.2 - h.1.2 := lt_of_not_ge hnot
      have hproductPositive :
          0 < (k.1.2 - h.1.2) * (ξh.1.2 : ℝ) :=
        mul_pos hsecondPositive hyH
      rw [hfirst] at hcrossH
      linarith [hcrossH, hproductPositive]
    apply Subtype.ext
    apply Prod.ext
    · exact hfirst
    · linarith

end LPP.Busemann
