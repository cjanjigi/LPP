/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# One-sided derivatives of finite concave profiles

This file proves the existence and order of the actual left and right
derivatives of a finite real-valued concave function at an interior point.
It also gives the differentiability criterion used for a scalar concave
profile.

## Main results

- `ConcaveOn.hasDerivWithinAt_leftDeriv_of_mem_interior` and
  `ConcaveOn.hasDerivWithinAt_rightDeriv_of_mem_interior` produce the actual
  derivatives represented by the corresponding `derivWithin` values.
- `ConcaveOn.rightDeriv_le_leftDeriv_of_mem_interior` orders those values.
- `ConcaveOn.differentiableAt_iff_leftDeriv_eq_rightDeriv_of_mem_interior`
  characterizes ordinary differentiability by equality of the two values.

The proof uses Mathlib's convex interior derivative results on the negative
of the concave function, then identifies the transported derivatives with
the canonical derivatives of the original function.
-/

public section

open Set
open Filter
open scoped Topology

namespace ConcaveOn

variable {S : Set ℝ} {f : ℝ → ℝ} {x : ℝ}

/-- A finite concave function has its canonical left derivative at an interior point. -/
theorem hasDerivWithinAt_leftDeriv_of_mem_interior
    (hconc : ConcaveOn ℝ S f) (hx : x ∈ interior S) :
    HasDerivWithinAt f (derivWithin f (Iio x) x) (Iio x) x := by
  have hconv : ConvexOn ℝ S (-f) := hconc.neg
  have hleft : HasDerivWithinAt f (-derivWithin (-f) (Iio x) x) (Iio x) x := by
    simpa only [neg_neg] using
      (hconv.hasDerivWithinAt_leftDeriv_of_mem_interior hx).neg
  rw [hleft.derivWithin (uniqueDiffWithinAt_Iio x)]
  exact hleft

/-- A finite concave function has its canonical right derivative at an interior point. -/
theorem hasDerivWithinAt_rightDeriv_of_mem_interior
    (hconc : ConcaveOn ℝ S f) (hx : x ∈ interior S) :
    HasDerivWithinAt f (derivWithin f (Ioi x) x) (Ioi x) x := by
  have hconv : ConvexOn ℝ S (-f) := hconc.neg
  have hright : HasDerivWithinAt f (-derivWithin (-f) (Ioi x) x) (Ioi x) x := by
    simpa only [neg_neg] using
      (hconv.hasDerivWithinAt_rightDeriv_of_mem_interior hx).neg
  rw [hright.derivWithin (uniqueDiffWithinAt_Ioi x)]
  exact hright

/-- For a finite concave function, the right derivative is at most the left one. -/
theorem rightDeriv_le_leftDeriv_of_mem_interior
    (hconc : ConcaveOn ℝ S f) (hx : x ∈ interior S) :
    derivWithin f (Ioi x) x ≤ derivWithin f (Iio x) x := by
  have hconv : ConvexOn ℝ S (-f) := hconc.neg
  have hleft : HasDerivWithinAt f (-derivWithin (-f) (Iio x) x) (Iio x) x := by
    simpa only [neg_neg] using
      (hconv.hasDerivWithinAt_leftDeriv_of_mem_interior hx).neg
  have hright : HasDerivWithinAt f (-derivWithin (-f) (Ioi x) x) (Ioi x) x := by
    simpa only [neg_neg] using
      (hconv.hasDerivWithinAt_rightDeriv_of_mem_interior hx).neg
  rw [hright.derivWithin (uniqueDiffWithinAt_Ioi x),
    hleft.derivWithin (uniqueDiffWithinAt_Iio x)]
  exact neg_le_neg (hconv.leftDeriv_le_rightDeriv_of_mem_interior hx)

/-- A finite concave function is differentiable at an interior point exactly
when its canonical left and right derivatives agree. -/
theorem differentiableAt_iff_leftDeriv_eq_rightDeriv_of_mem_interior
    (hconc : ConcaveOn ℝ S f) (hx : x ∈ interior S) :
    DifferentiableAt ℝ f x ↔ derivWithin f (Iio x) x = derivWithin f (Ioi x) x := by
  have hleft := hconc.hasDerivWithinAt_leftDeriv_of_mem_interior hx
  have hright := hconc.hasDerivWithinAt_rightDeriv_of_mem_interior hx
  have hleft_slope :
      Tendsto (slope f x) (𝓝[<] x) (𝓝 (derivWithin f (Iio x) x)) := by
    have h := hasDerivWithinAt_iff_tendsto_slope.mp hleft
    simpa only [sdiff_singleton_eq_self (by simp : x ∉ Iio x)] using h
  have hright_slope :
      Tendsto (slope f x) (𝓝[>] x) (𝓝 (derivWithin f (Ioi x) x)) := by
    have h := hasDerivWithinAt_iff_tendsto_slope.mp hright
    simpa only [sdiff_singleton_eq_self (by simp : x ∉ Ioi x)] using h
  constructor
  · intro hdiff
    have hderiv : HasDerivAt f (deriv f x) x := hdiff.hasDerivAt
    rcases hasDerivAt_iff_tendsto_slope_left_right.mp hderiv with
      ⟨hleft_deriv, hright_deriv⟩
    have hleft_eq : derivWithin f (Iio x) x = deriv f x :=
      tendsto_nhds_unique hleft_slope hleft_deriv
    have hright_eq : derivWithin f (Ioi x) x = deriv f x :=
      tendsto_nhds_unique hright_slope hright_deriv
    rw [hleft_eq, hright_eq]
  · intro hEq
    have hright_slope' :
        Tendsto (slope f x) (𝓝[>] x) (𝓝 (derivWithin f (Iio x) x)) := by
      simpa only [hEq] using hright_slope
    have hderiv : HasDerivAt f (derivWithin f (Iio x) x) x :=
      hasDerivAt_iff_tendsto_slope_left_right.mpr ⟨hleft_slope, hright_slope'⟩
    exact hderiv.differentiableAt

end ConcaveOn

