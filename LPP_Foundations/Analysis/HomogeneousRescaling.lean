/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Analysis.Quadrant
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Tactic.Ring

/-!
# Positive rescaling and differentiability

The auxiliary extension of a positively homogeneous quadrant function
inherits homogeneity on the whole real plane. Positive scalar multiplication
then preserves differentiability at the correspondingly scaled point.
-/

public section

open Filter
open scoped NNReal

namespace LPPDifferentiability

/-- The quadrant extension is homogeneous under nonnegative scaling,
including at points with a negative coordinate. -/
theorem quadrantExtension_smul
    (g : Quadrant → ℝ)
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z)
    (c : ℝ≥0) (x : ℝ × ℝ) :
    quadrantExtension g (c • x) = (c : ℝ) * quadrantExtension g x := by
  have hcoords : toQuadrant (c • x) = c • toQuadrant x := by
    apply Prod.ext
    · change Real.toNNReal ((c : ℝ) * x.1) = c * Real.toNNReal x.1
      calc
        Real.toNNReal ((c : ℝ) * x.1) =
            Real.toNNReal (c : ℝ) * Real.toNNReal x.1 := Real.toNNReal_mul c.2
        _ = c * Real.toNNReal x.1 := by rw [Real.toNNReal_coe]
    · change Real.toNNReal ((c : ℝ) * x.2) = c * Real.toNNReal x.2
      calc
        Real.toNNReal ((c : ℝ) * x.2) =
            Real.toNNReal (c : ℝ) * Real.toNNReal x.2 := Real.toNNReal_mul c.2
        _ = c * Real.toNNReal x.2 := by rw [Real.toNNReal_coe]
  change g (toQuadrant (c • x)) = (c : ℝ) * g (toQuadrant x)
  rw [hcoords]
  exact hhom c (toQuadrant x)

/-- Differentiability of the extension is invariant under every positive
rescaling. The zero scalar is excluded because its map is not invertible. -/
theorem differentiableAt_quadrantExtension_smul_iff
    (g : Quadrant → ℝ)
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z)
    (c : ℝ≥0) (hc : 0 < c) (x : ℝ × ℝ) :
    DifferentiableAt ℝ (quadrantExtension g) (c • x) ↔
      DifferentiableAt ℝ (quadrantExtension g) x := by
  constructor
  · intro hcx
    have hscale : DifferentiableAt ℝ (fun y : ℝ × ℝ => c • y) x :=
      differentiableAt_id.const_smul c
    have hcomp : DifferentiableAt ℝ
        (fun y : ℝ × ℝ => quadrantExtension g (c • y)) x :=
      hcx.comp (f := fun y : ℝ × ℝ => c • y)
        (g := quadrantExtension g) x hscale
    have hscaled : DifferentiableAt ℝ (c • quadrantExtension g) x := by
      apply hcomp.congr_of_eventuallyEq
      exact Eventually.of_forall (fun y => (quadrantExtension_smul g hhom c y).symm)
    exact
      (@differentiableAt_smul_iff ℝ _ (ℝ × ℝ) _ _ ℝ _ _ (quadrantExtension g) x
        ℝ≥0 _ _ _ _ c (invertibleOfNonzero hc.ne')).mp hscaled
  · intro hx
    have hscale : c⁻¹ • (c • x) = x := by
      rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
    have hbase : DifferentiableAt ℝ (quadrantExtension g)
        (c⁻¹ • (c • x)) := by
      simpa only [hscale] using hx
    have hscale' : DifferentiableAt ℝ (fun y : ℝ × ℝ => c⁻¹ • y) (c • x) :=
      differentiableAt_id.const_smul c⁻¹
    have hcomp : DifferentiableAt ℝ
        (fun y : ℝ × ℝ => quadrantExtension g (c⁻¹ • y)) (c • x) :=
      hbase.comp (f := fun y : ℝ × ℝ => c⁻¹ • y)
        (g := quadrantExtension g) (c • x) hscale'
    have hscaled : DifferentiableAt ℝ (c⁻¹ • quadrantExtension g) (c • x) := by
      apply hcomp.congr_of_eventuallyEq
      exact Eventually.of_forall
        (fun y => (quadrantExtension_smul g hhom c⁻¹ y).symm)
    exact
      (@differentiableAt_smul_iff ℝ _ (ℝ × ℝ) _ _ ℝ _ _ (quadrantExtension g) (c • x)
        ℝ≥0 _ _ _ _ c⁻¹ (invertibleOfNonzero (inv_ne_zero hc.ne'))).mp hscaled

/-- At a point with positive coordinates, differentiability is equivalent to
differentiability at its unit-sum normalization. -/
theorem differentiableAt_quadrantExtension_iff_normalized
    (g : Quadrant → ℝ)
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z)
    (x : ℝ × ℝ) (hx₁ : 0 < x.1) (hx₂ : 0 < x.2) :
    DifferentiableAt ℝ (quadrantExtension g) x ↔
      DifferentiableAt ℝ (quadrantExtension g)
        (x.1 / (x.1 + x.2), x.2 / (x.1 + x.2)) := by
  let s : ℝ := x.1 + x.2
  have hs : 0 < s := add_pos hx₁ hx₂
  let c : ℝ≥0 := ⟨s⁻¹, inv_nonneg.mpr hs.le⟩
  have hc : 0 < c := by
    change 0 < s⁻¹
    exact inv_pos.mpr hs
  have hcoords : c • x = (x.1 / s, x.2 / s) := by
    apply Prod.ext
    · change s⁻¹ * x.1 = x.1 / s
      rw [div_eq_mul_inv]
      ring
    · change s⁻¹ * x.2 = x.2 / s
      rw [div_eq_mul_inv]
      ring
  simpa only [hcoords] using
    (differentiableAt_quadrantExtension_smul_iff g hhom c hc x).symm

end LPPDifferentiability
