/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.Definitions.SupportsAt
public import LPP_Foundations.Analysis.ShapeCoordinateDerivatives
import Busemann.Geometry.SupportIdentities
import LPP_Foundations.Analysis.ShapeSupportingFunctionals
import LPP_Foundations.Analysis.ShapeExtremeSlopes
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Concrete coordinate-gradient supports

The literal negative coordinate one-sided gradients support the shape and bound
the first coordinate of every other support at the chosen interior direction.
-/

public section

open Set LPPDifferentiability
open scoped NNReal

namespace LPP.Busemann

/-- The negative coordinate-gradient pairs are supports, and their first tilt
coordinates bound every support at the direction. These are the source left
and right gradients in JR1810.03580v3, Section 2.3 and Lemma 4.7(c). -/
theorem coordinate_extreme_tilts_support_and_order
    (g : Quadrant → ℝ)
    (hconc : ∀ (x y : Quadrant) (r s : ℝ≥0), r + s = 1 →
      (r : ℝ) * g x + (s : ℝ) * g y ≤ g (r • x + s • y))
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z)
    (ξ : InteriorDirection) :
    let a : ℝ := (ξ.1.1 : ℝ)
    let U1 : ℝ → ℝ := fun t => quadrantExtension g (a + t, 1 - a)
    let U2 : ℝ → ℝ := fun t => quadrantExtension g (a, 1 - a + t)
    let hleft : ℝ × ℝ :=
      (-derivWithin U1 (Iio 0) 0, -derivWithin U2 (Ioi 0) 0)
    let hright : ℝ × ℝ :=
      (-derivWithin U1 (Ioi 0) 0, -derivWithin U2 (Iio 0) 0)
    SupportsAt g ξ hleft ∧ SupportsAt g ξ hright ∧
      ∀ k : ℝ × ℝ, SupportsAt g ξ k → hleft.1 ≤ k.1 ∧ k.1 ≤ hright.1 := by
  let a : ℝ := (ξ.1.1 : ℝ)
  let U1 : ℝ → ℝ := fun t => quadrantExtension g (a + t, 1 - a)
  let U2 : ℝ → ℝ := fun t => quadrantExtension g (a, 1 - a + t)
  let hleft : ℝ × ℝ :=
    (-derivWithin U1 (Iio 0) 0, -derivWithin U2 (Ioi 0) 0)
  let hright : ℝ × ℝ :=
    (-derivWithin U1 (Ioi 0) 0, -derivWithin U2 (Iio 0) 0)
  let H : ℝ → ℝ := fun t => quadrantExtension g (a + t, 1 - a - t)
  let dl : ℝ := derivWithin H (Iio 0) 0
  let dr : ℝ := derivWithin H (Ioi 0) 0
  change SupportsAt g ξ hleft ∧ SupportsAt g ξ hright ∧
    ∀ k : ℝ × ℝ, SupportsAt g ξ k → hleft.1 ≤ k.1 ∧ k.1 ≤ hright.1
  have ha₀ : 0 < a := by exact_mod_cast ξ.2.1
  have hξ₂pos : 0 < (ξ.1.2 : ℝ) := by exact_mod_cast ξ.2.2.1
  have hξ₂ : (ξ.1.2 : ℝ) = 1 - a := by
    dsimp only [a]
    linarith only [ξ.2.2.2]
  have ha₁ : a < 1 := by linarith only [hξ₂pos, hξ₂]
  have hξcoords : quadrantInclusion ξ.1 = (a, 1 - a) := Prod.ext rfl hξ₂
  have hvalue : quadrantExtension g (a, 1 - a) = g ξ.1 := by
    rw [← hξcoords, quadrantExtension_quadrantInclusion]
  have hzero : H 0 = g ξ.1 := by
    simpa only [H, add_zero, sub_zero] using hvalue
  -- Consume the coordinate derivatives, including the reversal of the second side.
  have hU1left : derivWithin U1 (Iio 0) 0 = H 0 + (1 - a) * dl := by
    simpa only [U1, H, dl, add_zero, sub_zero] using
      (hasDerivWithinAt_first_coordinate_left g hconc hhom a ha₀ ha₁).derivWithin
        (uniqueDiffWithinAt_Iio 0)
  have hU1right : derivWithin U1 (Ioi 0) 0 = H 0 + (1 - a) * dr := by
    simpa only [U1, H, dr, add_zero, sub_zero] using
      (hasDerivWithinAt_first_coordinate_right g hconc hhom a ha₀ ha₁).derivWithin
        (uniqueDiffWithinAt_Ioi 0)
  have hU2right : derivWithin U2 (Ioi 0) 0 = H 0 - a * dl := by
    simpa only [U2, H, dl, add_zero, sub_zero] using
      (hasDerivWithinAt_second_coordinate_right g hconc hhom a ha₀ ha₁).derivWithin
        (uniqueDiffWithinAt_Ioi 0)
  have hU2left : derivWithin U2 (Iio 0) 0 = H 0 - a * dr := by
    simpa only [U2, H, dr, add_zero, sub_zero] using
      (hasDerivWithinAt_second_coordinate_left g hconc hhom a ha₀ ha₁).derivWithin
        (uniqueDiffWithinAt_Iio 0)
  have hleftForm : hleft = (-(H 0 + (1 - a) * dl), -(H 0 - a * dl)) := by
    dsimp only [hleft]
    rw [hU1left, hU2right]
  have hrightForm : hright = (-(H 0 + (1 - a) * dr), -(H 0 - a * dr)) := by
    dsimp only [hright]
    rw [hU1right, hU2left]
  -- The supporting functionals give the global upper bounds.
  have hsupports := quadrant_supporting_functionals_and_contact g hconc hhom a ha₀ ha₁
  have hmajorantLeft : ∀ z : Quadrant,
      g z ≤ (H 0 + (1 - a) * dl) * (z.1 : ℝ) + (H 0 - a * dl) * (z.2 : ℝ) := by
    intro z
    calc
      g z ≤ H 0 * ((z.1 : ℝ) + (z.2 : ℝ)) +
          dl * ((1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ)) := (hsupports.1 z).1
      _ = (H 0 + (1 - a) * dl) * (z.1 : ℝ) +
          (H 0 - a * dl) * (z.2 : ℝ) := by ring
  have hmajorantRight : ∀ z : Quadrant,
      g z ≤ (H 0 + (1 - a) * dr) * (z.1 : ℝ) + (H 0 - a * dr) * (z.2 : ℝ) := by
    intro z
    calc
      g z ≤ H 0 * ((z.1 : ℝ) + (z.2 : ℝ)) +
          dr * ((1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ)) := (hsupports.1 z).2
      _ = (H 0 + (1 - a) * dr) * (z.1 : ℝ) +
          (H 0 - a * dr) * (z.2 : ℝ) := by ring
  have hleftSupport : SupportsAt g ξ hleft := by
    apply (supportsAt_iff_through_origin_majorant_and_contact g ξ hleft hhom).mpr
    rw [hleftForm]
    simp only [neg_neg]
    refine ⟨hmajorantLeft, ?_⟩
    change g ξ.1 = (H 0 + (1 - a) * dl) * a + (H 0 - a * dl) * (ξ.1.2 : ℝ)
    rw [← hzero, hξ₂]
    ring
  have hrightSupport : SupportsAt g ξ hright := by
    apply (supportsAt_iff_through_origin_majorant_and_contact g ξ hright hhom).mpr
    rw [hrightForm]
    simp only [neg_neg]
    refine ⟨hmajorantRight, ?_⟩
    change g ξ.1 = (H 0 + (1 - a) * dr) * a + (H 0 - a * dr) * (ξ.1.2 : ℝ)
    rw [← hzero, hξ₂]
    ring
  refine ⟨hleftSupport, hrightSupport, ?_⟩
  -- Every support has Euler contact, so the slope comparison applies.
  intro k hk
  have hkmajorant := (supportsAt_iff_through_origin_majorant_and_contact g ξ k hhom).mp hk
  have hkcontact : quadrantExtension g (a, 1 - a) =
      (-k.1) * a + (-k.2) * (1 - a) := by
    rw [hvalue]
    simpa only [hξ₂] using hkmajorant.2
  have hbounds := first_coordinate_bounds_of_touching_majorant
    g hconc a ha₀ ha₁ (-k.1) (-k.2) hkmajorant.1 hkcontact
  change H 0 + (1 - a) * dr ≤ -k.1 ∧ -k.1 ≤ H 0 + (1 - a) * dl at hbounds
  rw [hleftForm, hrightForm]
  change -(H 0 + (1 - a) * dl) ≤ k.1 ∧ k.1 ≤ -(H 0 + (1 - a) * dr)
  constructor
  · linarith only [hbounds.2]
  · linarith only [hbounds.1]

end LPP.Busemann
