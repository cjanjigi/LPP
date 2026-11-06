/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Analysis.ConcaveProfileSlopes
public import LPP_Foundations.Analysis.HomogeneousDifferentiability
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Concavity and derivatives of the shape profile

The profile on the closed unit-sum segment is concave when the quadrant function satisfies
its weighted concavity inequality. Its canonical one-sided derivatives then exist and are
ordered at interior parameters. For a nonnegatively homogeneous quadrant function, their
equality characterizes ambient differentiability of the quadrant extension.
-/

public section

open Set
open scoped Topology NNReal

namespace LPPDifferentiability

/-- Concavity of the function on the nonnegative quadrant produces concavity of its profile
on the closed interval `[-a, 1 - a]`. -/
theorem concaveOn_quadrantExtension_profile
    (g : Quadrant → ℝ)
    (hgconc : ∀ (x y : Quadrant) (r s : ℝ≥0), r + s = 1 →
      (r : ℝ) * g x + (s : ℝ) * g y ≤ g (r • x + s • y))
    (a : ℝ) :
    ConcaveOn ℝ (Icc (-a) (1 - a))
      (fun h : ℝ => quadrantExtension g (a + h, 1 - a - h)) := by
  refine ⟨convex_Icc (-a) (1 - a), ?_⟩
  intro x hx y hy t u ht hu htu
  let r : ℝ≥0 := ⟨t, ht⟩
  let s : ℝ≥0 := ⟨u, hu⟩
  have hrs : r + s = 1 := by
    apply NNReal.coe_injective
    change t + u = 1
    exact htu
  have hmix_mem : t • x + u • y ∈ Icc (-a) (1 - a) :=
    (convex_Icc (-a) (1 - a)) hx hy ht hu htu
  have hx₁ : 0 ≤ a + x := by linarith [hx.1]
  have hx₂ : 0 ≤ 1 - a - x := by linarith [hx.2]
  have hy₁ : 0 ≤ a + y := by linarith [hy.1]
  have hy₂ : 0 ≤ 1 - a - y := by linarith [hy.2]
  have hmix₁ : 0 ≤ a + (t * x + u * y) := by
    change 0 ≤ a + (t • x + u • y)
    linarith [hmix_mem.1]
  have hmix₂ : 0 ≤ 1 - a - (t * x + u * y) := by
    change 0 ≤ 1 - a - (t • x + u • y)
    linarith [hmix_mem.2]
  let qx : Quadrant := toQuadrant (a + x, 1 - a - x)
  let qy : Quadrant := toQuadrant (a + y, 1 - a - y)
  have hq : r • qx + s • qy =
      toQuadrant (a + (t * x + u * y), 1 - a - (t * x + u * y)) := by
    apply Prod.ext
    · apply NNReal.coe_injective
      change (r : ℝ) * ((a + x).toNNReal : ℝ) +
          (s : ℝ) * ((a + y).toNNReal : ℝ) =
        ((a + (t * x + u * y)).toNNReal : ℝ)
      rw [Real.coe_toNNReal _ hx₁, Real.coe_toNNReal _ hy₁,
        Real.coe_toNNReal _ hmix₁]
      rw [show (r : ℝ) = t from rfl, show (s : ℝ) = u from rfl]
      calc
        t * (a + x) + u * (a + y) = a * (t + u) + (t * x + u * y) := by ring
        _ = a + (t * x + u * y) := by rw [htu, mul_one]
    · apply NNReal.coe_injective
      change (r : ℝ) * ((1 - a - x).toNNReal : ℝ) +
          (s : ℝ) * ((1 - a - y).toNNReal : ℝ) =
        ((1 - a - (t * x + u * y)).toNNReal : ℝ)
      rw [Real.coe_toNNReal _ hx₂, Real.coe_toNNReal _ hy₂,
        Real.coe_toNNReal _ hmix₂]
      rw [show (r : ℝ) = t from rfl, show (s : ℝ) = u from rfl]
      calc
        t * (1 - a - x) + u * (1 - a - y) =
            (1 - a) * (t + u) - (t * x + u * y) := by ring
        _ = 1 - a - (t * x + u * y) := by rw [htu, mul_one]
  change t * g qx + u * g qy ≤
    g (toQuadrant (a + (t * x + u * y), 1 - a - (t * x + u * y)))
  have hg := hgconc qx qy r s hrs
  rw [show (r : ℝ) = t from rfl, show (s : ℝ) = u from rfl] at hg
  rw [← hq]
  exact hg

/-- The profile has its canonical left derivative at every
interior unit-sum parameter. -/
theorem hasDerivWithinAt_profile_left
    (g : Quadrant → ℝ)
    (hgconc : ∀ (x y : Quadrant) (r s : ℝ≥0), r + s = 1 →
      (r : ℝ) * g x + (s : ℝ) * g y ≤ g (r • x + s • y))
    (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) :
    HasDerivWithinAt
      (fun h : ℝ => quadrantExtension g (a + h, 1 - a - h))
      (derivWithin (fun h : ℝ => quadrantExtension g (a + h, 1 - a - h))
        (Iio 0) 0) (Iio 0) 0 := by
  have hprofile := concaveOn_quadrantExtension_profile g hgconc a
  have hzero : (0 : ℝ) ∈ interior (Icc (-a) (1 - a)) := by
    rw [interior_Icc]
    constructor <;> linarith
  exact hprofile.hasDerivWithinAt_leftDeriv_of_mem_interior hzero

/-- The profile has its canonical right derivative at every
interior unit-sum parameter. -/
theorem hasDerivWithinAt_profile_right
    (g : Quadrant → ℝ)
    (hgconc : ∀ (x y : Quadrant) (r s : ℝ≥0), r + s = 1 →
      (r : ℝ) * g x + (s : ℝ) * g y ≤ g (r • x + s • y))
    (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) :
    HasDerivWithinAt
      (fun h : ℝ => quadrantExtension g (a + h, 1 - a - h))
      (derivWithin (fun h : ℝ => quadrantExtension g (a + h, 1 - a - h))
        (Ioi 0) 0) (Ioi 0) 0 := by
  have hprofile := concaveOn_quadrantExtension_profile g hgconc a
  have hzero : (0 : ℝ) ∈ interior (Icc (-a) (1 - a)) := by
    rw [interior_Icc]
    constructor <;> linarith
  exact hprofile.hasDerivWithinAt_rightDeriv_of_mem_interior hzero

/-- The right profile derivative is at most the left profile derivative. -/
theorem profile_rightDeriv_le_leftDeriv
    (g : Quadrant → ℝ)
    (hgconc : ∀ (x y : Quadrant) (r s : ℝ≥0), r + s = 1 →
      (r : ℝ) * g x + (s : ℝ) * g y ≤ g (r • x + s • y))
    (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) :
    derivWithin (fun h : ℝ => quadrantExtension g (a + h, 1 - a - h))
      (Ioi 0) 0 ≤
    derivWithin (fun h : ℝ => quadrantExtension g (a + h, 1 - a - h))
      (Iio 0) 0 := by
  have hprofile := concaveOn_quadrantExtension_profile g hgconc a
  have hzero : (0 : ℝ) ∈ interior (Icc (-a) (1 - a)) := by
    rw [interior_Icc]
    constructor <;> linarith
  exact hprofile.rightDeriv_le_leftDeriv_of_mem_interior hzero

/-- For a nonnegatively homogeneous quadrant function, ambient
differentiability is equivalent to equality of the two canonical
derivatives of its concave profile. -/
theorem differentiableAt_quadrantExtension_iff_profile_derivatives_eq
    (g : Quadrant → ℝ)
    (hgconc : ∀ (x y : Quadrant) (r s : ℝ≥0), r + s = 1 →
      (r : ℝ) * g x + (s : ℝ) * g y ≤ g (r • x + s • y))
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z)
    (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) :
    DifferentiableAt ℝ (quadrantExtension g) (a, 1 - a) ↔
      derivWithin (fun h : ℝ => quadrantExtension g (a + h, 1 - a - h))
          (Iio 0) 0 =
        derivWithin (fun h : ℝ => quadrantExtension g (a + h, 1 - a - h))
          (Ioi 0) 0 := by
  have hprofile := concaveOn_quadrantExtension_profile g hgconc a
  have hzero : (0 : ℝ) ∈ interior (Icc (-a) (1 - a)) := by
    rw [interior_Icc]
    constructor <;> linarith
  exact
    (differentiableAt_profile_iff_quadrantExtension g hhom a ha₀ ha₁).symm.trans
      (hprofile.differentiableAt_iff_leftDeriv_eq_rightDeriv_of_mem_interior hzero)

end LPPDifferentiability
