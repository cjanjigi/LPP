/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Analysis.QuadrantSuperdifferential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Homogeneous majorants and the quadrant superdifferential

For a homogeneous function on the full closed quadrant, a supergradient is
exactly a linear majorant with equality at the contact point.
-/

public section

open LPPDifferentiability
open scoped NNReal

namespace LPPDifferentiability

/-- For a degree-one homogeneous function on the full closed quadrant,
superdifferential membership is equivalent to a global linear majorant with
contact at the chosen point. No interior or normalization assumption is used. -/
theorem mem_quadrantSuperdifferential_iff_majorant_and_contact
    (g : Quadrant → ℝ) (ξ : Quadrant) (v : ℝ × ℝ)
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant),
      g (c • z) = (c : ℝ) * g z) :
    (v ∈ quadrantSuperdifferential g ξ ↔
      (∀ z : Quadrant,
        g z ≤ v.1 * (z.1 : ℝ) + v.2 * (z.2 : ℝ)) ∧
      g ξ = v.1 * (ξ.1 : ℝ) + v.2 * (ξ.2 : ℝ)) := by
  let affine : Quadrant → ℝ := fun z =>
    v.1 * (z.1 : ℝ) + v.2 * (z.2 : ℝ)
  change (∀ z : Quadrant,
      v.1 * ((ξ.1 : ℝ) - (z.1 : ℝ)) +
        v.2 * ((ξ.2 : ℝ) - (z.2 : ℝ)) ≤ g ξ - g z) ↔
    (∀ z : Quadrant, g z ≤ affine z) ∧ g ξ = affine ξ
  constructor
  · intro hsupp
    have hzeroSmul : (0 : ℝ≥0) • (0 : Quadrant) = 0 := by
      change ((0 : ℝ≥0) * (0 : ℝ≥0), (0 : ℝ≥0) * (0 : ℝ≥0)) = (0, 0)
      simp
    have hzero : g (0 : Quadrant) = 0 := by
      simpa only [hzeroSmul, NNReal.coe_zero, zero_mul] using hhom 0 0
    have hcontactLower : affine ξ ≤ g ξ := by
      simpa [affine, hzero] using hsupp 0
    have hcontactUpper : g ξ ≤ affine ξ := by
      have hsuppTwice := hsupp ((2 : ℝ≥0) • ξ)
      simp [hhom] at hsuppTwice
      nlinarith [hsuppTwice]
    have hcontact : g ξ = affine ξ :=
      le_antisymm hcontactUpper hcontactLower
    have hmajorant : ∀ z : Quadrant, g z ≤ affine z := by
      intro z
      have hshift : affine ξ - affine z ≤ g ξ - g z := by
        calc
          affine ξ - affine z =
              v.1 * ((ξ.1 : ℝ) - (z.1 : ℝ)) +
                v.2 * ((ξ.2 : ℝ) - (z.2 : ℝ)) := by
                  simp [affine]
                  ring
          _ ≤ g ξ - g z := hsupp z
      change g z ≤ affine z
      linarith [hshift, hcontact]
    exact ⟨hmajorant, hcontact⟩
  · rintro ⟨hmajorant, hcontact⟩ z
    have hshift : affine ξ - affine z ≤ g ξ - g z := by
      rw [hcontact]
      linarith [hmajorant z]
    calc
      v.1 * ((ξ.1 : ℝ) - (z.1 : ℝ)) +
          v.2 * ((ξ.2 : ℝ) - (z.2 : ℝ)) =
          affine ξ - affine z := by
            simp [affine]
            ring
      _ ≤ g ξ - g z := hshift

end LPPDifferentiability
