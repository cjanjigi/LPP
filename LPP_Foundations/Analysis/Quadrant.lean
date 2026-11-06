/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Analysis.QuadrantExtension
public import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# Inclusion of the quadrant in the real plane

Coordinate maps between the closed quadrant and the real plane. Two extensions of the same
function agree near each interior point, so differentiability of an extension at an interior
point does not depend on which extension is chosen.
-/

@[expose] public section

open Set Filter
open scoped Topology NNReal

namespace LPPDifferentiability

/-- Inclusion of the closed quadrant in the real plane. -/
def quadrantInclusion (z : Quadrant) : ℝ × ℝ := ((z.1 : ℝ), (z.2 : ℝ))

@[simp] theorem toQuadrant_quadrantInclusion (z : Quadrant) :
    toQuadrant (quadrantInclusion z) = z := by
  simp only [toQuadrant, quadrantInclusion, Real.toNNReal_coe]

@[simp] theorem quadrantExtension_quadrantInclusion (g : Quadrant → ℝ) (z : Quadrant) :
    quadrantExtension g (quadrantInclusion z) = g z := by
  exact congrArg g (toQuadrant_quadrantInclusion z)

theorem quadrantInclusion_toQuadrant (x : ℝ × ℝ) (hx₁ : 0 ≤ x.1) (hx₂ : 0 ≤ x.2) :
    quadrantInclusion (toQuadrant x) = x := by
  apply Prod.ext
  · exact Real.coe_toNNReal x.1 hx₁
  · exact Real.coe_toNNReal x.2 hx₂

theorem closedQuadrant_mem_nhds (x : ℝ × ℝ) (hx₁ : 0 < x.1) (hx₂ : 0 < x.2) :
    {y : ℝ × ℝ | 0 ≤ y.1 ∧ 0 ≤ y.2} ∈ 𝓝 x := by
  have h₁ : {y : ℝ × ℝ | 0 < y.1} ∈ 𝓝 x :=
    (isOpen_lt continuous_const continuous_fst).mem_nhds hx₁
  have h₂ : {y : ℝ × ℝ | 0 < y.2} ∈ 𝓝 x :=
    (isOpen_lt continuous_const continuous_snd).mem_nhds hx₂
  exact mem_of_superset (inter_mem h₁ h₂) (fun _ hy => ⟨hy.1.le, hy.2.le⟩)

/-- The quadrant extension agrees locally with any ambient extension of the
same function on the closed quadrant. -/
theorem eventuallyEq_quadrantExtension (g : Quadrant → ℝ) (h : ℝ × ℝ → ℝ)
    (hext : ∀ z : Quadrant, h (quadrantInclusion z) = g z)
    (x : ℝ × ℝ) (hx₁ : 0 < x.1) (hx₂ : 0 < x.2) :
    h =ᶠ[𝓝 x] quadrantExtension g := by
  filter_upwards [closedQuadrant_mem_nhds x hx₁ hx₂] with y hy
  change h y = g (toQuadrant y)
  rw [← hext (toQuadrant y), quadrantInclusion_toQuadrant y hy.1 hy.2]

theorem differentiableAt_quadrantExtension_iff (g : Quadrant → ℝ) (h : ℝ × ℝ → ℝ)
    (hext : ∀ z : Quadrant, h (quadrantInclusion z) = g z)
    (x : ℝ × ℝ) (hx₁ : 0 < x.1) (hx₂ : 0 < x.2) :
    DifferentiableAt ℝ h x ↔ DifferentiableAt ℝ (quadrantExtension g) x :=
  (eventuallyEq_quadrantExtension g h hext x hx₁ hx₂).differentiableAt_iff

theorem differentiableWithinAt_closedQuadrant_iff (g : Quadrant → ℝ)
    (x : ℝ × ℝ) (hx₁ : 0 < x.1) (hx₂ : 0 < x.2) :
    DifferentiableWithinAt ℝ (quadrantExtension g)
      {y | 0 ≤ y.1 ∧ 0 ≤ y.2} x ↔
      DifferentiableAt ℝ (quadrantExtension g) x := by
  constructor
  · intro h
    exact h.differentiableAt (closedQuadrant_mem_nhds x hx₁ hx₂)
  · intro h
    exact h.differentiableWithinAt

end LPPDifferentiability
