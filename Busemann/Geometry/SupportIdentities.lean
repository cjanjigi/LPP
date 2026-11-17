/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.Definitions.SupportsAt
import LPP_Foundations.Analysis.QuadrantSuperdifferentialIdentities
import LPP_Foundations.Analysis.ShapeSupportingFunctionals

/-!
# Algebraic identities for Busemann supporting tilts

These lemmas record the contact and uniqueness consequences of the affine
support inequality. The homogeneous characterization uses only degree-one
homogeneity, while contact transfer needs no homogeneity.
-/

public section

open LPPDifferentiability
open scoped NNReal

namespace LPP.Busemann

/-- For a degree-one homogeneous shape, an interior support is a global
through-origin affine upper bound that agrees with the shape at the supported
direction. The support inequality is JR arXiv:1810.03580v3, equation (2.5). -/
theorem supportsAt_iff_through_origin_majorant_and_contact
    (g : Quadrant → ℝ) (ξ : InteriorDirection) (h : ℝ × ℝ)
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant),
      g (c • z) = (c : ℝ) * g z) :
    SupportsAt g ξ h ↔
      (∀ z : Quadrant,
        g z ≤ (-h.1) * (z.1 : ℝ) + (-h.2) * (z.2 : ℝ)) ∧
      g ξ.1 = (-h.1) * (ξ.1.1 : ℝ) + (-h.2) * (ξ.1.2 : ℝ) := by
  change (-h.1, -h.2) ∈ quadrantSuperdifferential g ξ.1 ↔
    (∀ z : Quadrant,
      g z ≤ (-h.1) * (z.1 : ℝ) + (-h.2) * (z.2 : ℝ)) ∧
    g ξ.1 = (-h.1) * (ξ.1.1 : ℝ) + (-h.2) * (ξ.1.2 : ℝ)
  exact mem_quadrantSuperdifferential_iff_majorant_and_contact
    g ξ.1 (-h.1, -h.2) hhom

/-- Once a tilt supports one direction, it supports another exactly when the
shape increment matches the affine increment of that tilt. This is the contact
set identity for the affine support inequality in JR arXiv:1810.03580v3,
equation (2.5). -/
theorem supportsAt_iff_affine_increment
    (g : Quadrant → ℝ) (ξ η : InteriorDirection) (h : ℝ × ℝ)
    (hsuppξ : SupportsAt g ξ h) :
    SupportsAt g η h ↔
      g η.1 - g ξ.1 =
        (-h.1) * ((η.1.1 : ℝ) - (ξ.1.1 : ℝ)) +
          (-h.2) * ((η.1.2 : ℝ) - (ξ.1.2 : ℝ)) := by
  let affine : Quadrant → ℝ := fun z =>
    (-h.1) * (z.1 : ℝ) + (-h.2) * (z.2 : ℝ)
  have hincrement : affine η.1 - affine ξ.1 =
      (-h.1) * ((η.1.1 : ℝ) - (ξ.1.1 : ℝ)) +
        (-h.2) * ((η.1.2 : ℝ) - (ξ.1.2 : ℝ)) := by
    simp [affine]
    ring
  constructor
  · intro hsuppη
    have hbackward : affine ξ.1 - affine η.1 ≤ g ξ.1 - g η.1 := by
      calc
        affine ξ.1 - affine η.1 =
            (-h.1) * ((ξ.1.1 : ℝ) - (η.1.1 : ℝ)) +
              (-h.2) * ((ξ.1.2 : ℝ) - (η.1.2 : ℝ)) := by
                simp [affine]
                ring
        _ ≤ g ξ.1 - g η.1 := hsuppξ η.1
    have hforward : affine η.1 - affine ξ.1 ≤ g η.1 - g ξ.1 := by
      calc
        affine η.1 - affine ξ.1 =
            (-h.1) * ((η.1.1 : ℝ) - (ξ.1.1 : ℝ)) +
              (-h.2) * ((η.1.2 : ℝ) - (ξ.1.2 : ℝ)) := by
                simp [affine]
                ring
        _ ≤ g η.1 - g ξ.1 := hsuppη ξ.1
    have hcontact : g η.1 - g ξ.1 = affine η.1 - affine ξ.1 := by
      linarith [hbackward, hforward]
    calc
      g η.1 - g ξ.1 = affine η.1 - affine ξ.1 := hcontact
      _ = (-h.1) * ((η.1.1 : ℝ) - (ξ.1.1 : ℝ)) +
            (-h.2) * ((η.1.2 : ℝ) - (ξ.1.2 : ℝ)) := hincrement
  · intro hcontact
    have hcontactAffine : g η.1 - g ξ.1 = affine η.1 - affine ξ.1 := by
      calc
        g η.1 - g ξ.1 =
            (-h.1) * ((η.1.1 : ℝ) - (ξ.1.1 : ℝ)) +
              (-h.2) * ((η.1.2 : ℝ) - (ξ.1.2 : ℝ)) := hcontact
        _ = affine η.1 - affine ξ.1 := hincrement.symm
    intro z
    have hξbound : affine ξ.1 - affine z ≤ g ξ.1 - g z := by
      calc
        affine ξ.1 - affine z =
            (-h.1) * ((ξ.1.1 : ℝ) - (z.1 : ℝ)) +
              (-h.2) * ((ξ.1.2 : ℝ) - (z.2 : ℝ)) := by
                simp [affine]
                ring
        _ ≤ g ξ.1 - g z := hsuppξ z
    have hηbound : affine η.1 - affine z ≤ g η.1 - g z := by
      linarith [hcontactAffine, hξbound]
    calc
      (-h.1) * ((η.1.1 : ℝ) - (z.1 : ℝ)) +
          (-h.2) * ((η.1.2 : ℝ) - (z.2 : ℝ)) =
          affine η.1 - affine z := by
            simp [affine]
            ring
      _ ≤ g η.1 - g z := hηbound

/-- At an interior direction, two degree-one homogeneous supports with the
same first tilt coordinate have the same second coordinate by Euler contact.
The support inequality is JR arXiv:1810.03580v3, equation (2.5). -/
theorem supporting_tilts_eq_of_first_coord_eq
    (g : Quadrant → ℝ) (ξ : InteriorDirection) (h k : ℝ × ℝ)
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant),
      g (c • z) = (c : ℝ) * g z)
    (hsupph : SupportsAt g ξ h) (hsuppk : SupportsAt g ξ k)
    (hfirst : h.1 = k.1) : h = k := by
  have heulerh : g ξ.1 =
      (-h.1) * (ξ.1.1 : ℝ) + (-h.2) * (ξ.1.2 : ℝ) :=
    ((supportsAt_iff_through_origin_majorant_and_contact g ξ h hhom).mp
      hsupph).2
  have heulerk : g ξ.1 =
      (-k.1) * (ξ.1.1 : ℝ) + (-k.2) * (ξ.1.2 : ℝ) :=
    ((supportsAt_iff_through_origin_majorant_and_contact g ξ k hhom).mp
      hsuppk).2
  apply Prod.ext
  · exact hfirst
  · have hsecondProduct :
        (-h.2) * (ξ.1.2 : ℝ) = (-k.2) * (ξ.1.2 : ℝ) := by
      calc
        (-h.2) * (ξ.1.2 : ℝ) =
            g ξ.1 - (-h.1) * (ξ.1.1 : ℝ) := by
              linarith [heulerh]
        _ = g ξ.1 - (-k.1) * (ξ.1.1 : ℝ) := by
              rw [hfirst]
        _ = (-k.2) * (ξ.1.2 : ℝ) := by
              linarith [heulerk]
    have hξ₂pos : 0 < (ξ.1.2 : ℝ) := by
      exact_mod_cast ξ.2.2.1
    have hξ₂ne : (ξ.1.2 : ℝ) ≠ 0 := ne_of_gt hξ₂pos
    have hsecondNeg : -h.2 = -k.2 :=
      mul_right_cancel₀ hξ₂ne hsecondProduct
    linarith

end LPP.Busemann
