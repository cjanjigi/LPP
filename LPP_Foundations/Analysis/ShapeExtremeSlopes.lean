/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Analysis.ShapeProfileCalculus
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Bounds on touching support coefficients

A specified linear majorant that touches a concave quadrant function at an
interior unit-sum direction has its transverse slope between the canonical
right and left profile derivatives. No homogeneity is needed for this comparison.
-/

public section

open Set Filter
open scoped Topology NNReal

namespace LPPDifferentiability

/-- A touching linear majorant has transverse slope between the right and left
profile derivatives. This is the elementary comparison used for the extreme
support coordinates in JR1810.03580v3, Section 2.3. -/
theorem profile_derivatives_bound_touching_majorant
    (g : Quadrant → ℝ)
    (hgconc : ∀ (x y : Quadrant) (r s : ℝ≥0), r + s = 1 →
      (r : ℝ) * g x + (s : ℝ) * g y ≤ g (r • x + s • y))
    (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) (p q : ℝ)
    (hsupport : ∀ z : Quadrant, g z ≤ p * (z.1 : ℝ) + q * (z.2 : ℝ))
    (hcontact : quadrantExtension g (a, 1 - a) = p * a + q * (1 - a)) :
    let H : ℝ → ℝ := fun t => quadrantExtension g (a + t, 1 - a - t)
    derivWithin H (Ioi 0) 0 ≤ p - q ∧
      p - q ≤ derivWithin H (Iio 0) 0 := by
  let H : ℝ → ℝ := fun t => quadrantExtension g (a + t, 1 - a - t)
  change derivWithin H (Ioi 0) 0 ≤ p - q ∧
    p - q ≤ derivWithin H (Iio 0) 0
  have hzero : H 0 = p * a + q * (1 - a) := by
    simpa only [H, add_zero, sub_zero] using hcontact
  -- Restrict the quadrant majorant to the profile and use contact at zero.
  have hprofile : ∀ t ∈ Icc (-a) (1 - a), H t ≤ H 0 + (p - q) * t := by
    intro t ht
    have hfirst : 0 ≤ a + t := by linarith only [ht.1]
    have hsecond : 0 ≤ 1 - a - t := by linarith only [ht.2]
    have hbound := hsupport (toQuadrant (a + t, 1 - a - t))
    change H t ≤ p * ((a + t).toNNReal : ℝ) +
      q * ((1 - a - t).toNNReal : ℝ) at hbound
    rw [Real.coe_toNNReal _ hfirst, Real.coe_toNNReal _ hsecond] at hbound
    calc
      H t ≤ p * (a + t) + q * (1 - a - t) := hbound
      _ = H 0 + (p - q) * t := by rw [hzero]; ring
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, t ∈ Ioo (-a) (1 - a) := by
    apply IsOpen.mem_nhds isOpen_Ioo
    constructor <;> linarith only [ha₀, ha₁]
  -- On the right, division by the positive displacement preserves order.
  have hrightSlope : ∀ᶠ t : ℝ in 𝓝[>] 0, slope H 0 t ≤ p - q := by
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht htpos
    rw [slope_def_field, sub_zero]
    apply (div_le_iff₀ htpos).2
    have hbound := hprofile t ⟨ht.1.le, ht.2.le⟩
    linarith only [hbound]
  -- On the left, division by the negative displacement reverses order.
  have hleftSlope : ∀ᶠ t : ℝ in 𝓝[<] 0, p - q ≤ slope H 0 t := by
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht htneg
    rw [slope_def_field, sub_zero]
    apply (le_div_iff_of_neg htneg).2
    have hbound := hprofile t ⟨ht.1.le, ht.2.le⟩
    linarith only [hbound]
  -- The already established one-sided derivatives are the limits of these slopes.
  have hright := hasDerivWithinAt_profile_right g hgconc a ha₀ ha₁
  have hleft := hasDerivWithinAt_profile_left g hgconc a ha₀ ha₁
  have hrightLimit : Tendsto (slope H 0) (𝓝[>] 0)
      (𝓝 (derivWithin H (Ioi 0) 0)) :=
    (hasDerivWithinAt_iff_tendsto_slope' (by simp only [mem_Ioi, lt_self_iff_false, not_false_eq_true])).1 hright
  have hleftLimit : Tendsto (slope H 0) (𝓝[<] 0)
      (𝓝 (derivWithin H (Iio 0) 0)) :=
    (hasDerivWithinAt_iff_tendsto_slope' (by simp only [mem_Iio, lt_self_iff_false, not_false_eq_true])).1 hleft
  exact ⟨le_of_tendsto hrightLimit hrightSlope, ge_of_tendsto hleftLimit hleftSlope⟩

/-- The first coefficient of a touching majorant lies between the two first
support coordinates determined by the profile derivatives. This is the
coordinate form of the comparison in JR1810.03580v3, Section 2.3. -/
theorem first_coordinate_bounds_of_touching_majorant
    (g : Quadrant → ℝ)
    (hgconc : ∀ (x y : Quadrant) (r s : ℝ≥0), r + s = 1 →
      (r : ℝ) * g x + (s : ℝ) * g y ≤ g (r • x + s • y))
    (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) (p q : ℝ)
    (hsupport : ∀ z : Quadrant, g z ≤ p * (z.1 : ℝ) + q * (z.2 : ℝ))
    (hcontact : quadrantExtension g (a, 1 - a) = p * a + q * (1 - a)) :
    let H : ℝ → ℝ := fun t => quadrantExtension g (a + t, 1 - a - t)
    H 0 + (1 - a) * derivWithin H (Ioi 0) 0 ≤ p ∧
      p ≤ H 0 + (1 - a) * derivWithin H (Iio 0) 0 := by
  let H : ℝ → ℝ := fun t => quadrantExtension g (a + t, 1 - a - t)
  change H 0 + (1 - a) * derivWithin H (Ioi 0) 0 ≤ p ∧
    p ≤ H 0 + (1 - a) * derivWithin H (Iio 0) 0
  have hzero : H 0 = p * a + q * (1 - a) := by
    simpa only [H, add_zero, sub_zero] using hcontact
  have hcoordinate : p = H 0 + (1 - a) * (p - q) := by
    rw [hzero]
    ring
  have hslopes := profile_derivatives_bound_touching_majorant
    g hgconc a ha₀ ha₁ p q hsupport hcontact
  have hfactor : 0 ≤ 1 - a := (sub_pos.mpr ha₁).le
  -- Contact expresses the first coefficient in terms of the transverse slope.
  constructor
  · calc
      H 0 + (1 - a) * derivWithin H (Ioi 0) 0 ≤
          H 0 + (1 - a) * (p - q) :=
        add_le_add (le_refl (H 0)) (mul_le_mul_of_nonneg_left hslopes.1 hfactor)
      _ = p := hcoordinate.symm
  · calc
      p = H 0 + (1 - a) * (p - q) := hcoordinate
      _ ≤ H 0 + (1 - a) * derivWithin H (Iio 0) 0 :=
        add_le_add (le_refl (H 0)) (mul_le_mul_of_nonneg_left hslopes.2 hfactor)

end LPPDifferentiability
