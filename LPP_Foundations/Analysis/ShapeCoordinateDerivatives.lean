/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Analysis.ShapeProfileCalculus
import LPP_Foundations.Analysis.HomogeneousRescaling
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Coordinate derivatives of the homogeneous shape

Positive normalization expresses each coordinate path through the transverse
profile. The first coordinate preserves profile sides; the second reverses them.
-/

public section

open Set Filter
open scoped Topology NNReal

namespace LPPDifferentiability

private theorem one_add_pos_eventually : ∀ᶠ t : ℝ in 𝓝 0, 0 < 1 + t := by
  have h : Ioi (-1 : ℝ) ∈ 𝓝 (0 : ℝ) := Ioi_mem_nhds (by norm_num)
  filter_upwards [h] with t ht
  change -1 < t at ht
  linarith only [ht]

private theorem coordinate_path_normalization
    (g : Quadrant → ℝ)
    (hhom : ∀ (r : ℝ≥0) (z : Quadrant), g (r • z) = (r : ℝ) * g z)
    (a c t : ℝ) (ht : 0 < 1 + t) :
    quadrantExtension g (a + (a + c) * t, 1 - a + (1 - a - c) * t) =
      (1 + t) * quadrantExtension g
        (a + c * t / (1 + t), 1 - a - c * t / (1 + t)) := by
  let r : ℝ≥0 := ⟨1 + t, ht.le⟩
  have hcoords : r • (a + c * t / (1 + t), 1 - a - c * t / (1 + t)) =
      (a + (a + c) * t, 1 - a + (1 - a - c) * t) := by
    apply Prod.ext
    · change (1 + t) * (a + c * t / (1 + t)) = a + (a + c) * t
      field_simp [ht.ne']
      ring
    · change (1 + t) * (1 - a - c * t / (1 + t)) =
        1 - a + (1 - a - c) * t
      field_simp [ht.ne']
      ring
  rw [← hcoords]
  exact quadrantExtension_smul g hhom r _

private theorem coordinate_path_hasDerivWithinAt
    (g : Quadrant → ℝ)
    (hhom : ∀ (r : ℝ≥0) (z : Quadrant), g (r • z) = (r : ℝ) * g z)
    (a c d : ℝ) (s v : Set ℝ)
    (hprofile : HasDerivWithinAt
      (fun t : ℝ => quadrantExtension g (a + t, 1 - a - t)) d v 0)
    (hmaps : ∀ᶠ t : ℝ in 𝓝[s] 0, c * t / (1 + t) ∈ v) :
    HasDerivWithinAt
      (fun t : ℝ => quadrantExtension g
        (a + (a + c) * t, 1 - a + (1 - a - c) * t))
      (quadrantExtension g (a, 1 - a) + c * d) s 0 := by
  let H : ℝ → ℝ := fun t => quadrantExtension g (a + t, 1 - a - t)
  let ratio : ℝ → ℝ := fun t => c * t / (1 + t)
  have hratio : HasDerivAt ratio c 0 := by
    have hnum := (hasDerivAt_id (0 : ℝ)).const_mul c
    have hden := (hasDerivAt_id (0 : ℝ)).const_add 1
    simpa only [ratio, id_eq, mul_zero, add_zero, mul_one,
      sub_zero, one_pow, div_one] using hnum.fun_div hden (by norm_num)
  have hratio_zero : ratio 0 = 0 := by
    dsimp only [ratio]
    rw [mul_zero, zero_div]
  -- The rational normalization tends to zero within the required profile side.
  have hmap : Tendsto ratio (𝓝[s] 0) (𝓝[v] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [hratio_zero] using
        hratio.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · exact hmaps
  have hpure : Tendsto ratio (pure 0) (pure 0) := by
    simpa only [hratio_zero] using tendsto_pure_pure ratio (0 : ℝ)
  have hcomp : HasDerivWithinAt (H ∘ ratio) (d * c) s 0 :=
    HasDerivAtFilter.comp hprofile hratio.hasDerivWithinAt (hmap.prodMap hpure)
  -- Differentiate the positive scale times the normalized profile.
  have hscale : HasDerivWithinAt (fun t : ℝ => 1 + t) 1 s 0 :=
    ((hasDerivAt_id (0 : ℝ)).const_add 1).hasDerivWithinAt
  have hproduct : HasDerivWithinAt (fun t : ℝ => (1 + t) * H (ratio t))
      (quadrantExtension g (a, 1 - a) + c * d) s 0 := by
    simpa only [Function.comp_apply, hratio_zero, add_zero, one_mul,
      H, sub_zero, mul_comm d c] using hscale.fun_mul hcomp
  apply hproduct.congr_of_eventuallyEq
  · filter_upwards [one_add_pos_eventually.filter_mono nhdsWithin_le_nhds] with t ht
    exact coordinate_path_normalization g hhom a c t ht
  · simp only [mul_zero, add_zero, H, ratio, zero_div, sub_zero, one_mul]

/-- The left first-coordinate derivative is the left transverse derivative
converted by homogeneity. This identifies the coordinate gradient in
JR1810.03580v3, Section 2.3. -/
theorem hasDerivWithinAt_first_coordinate_left
    (g : Quadrant → ℝ)
    (hgconc : ∀ (x y : Quadrant) (r s : ℝ≥0), r + s = 1 →
      (r : ℝ) * g x + (s : ℝ) * g y ≤ g (r • x + s • y))
    (hhom : ∀ (r : ℝ≥0) (z : Quadrant), g (r • z) = (r : ℝ) * g z)
    (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) :
    let H : ℝ → ℝ := fun t => quadrantExtension g (a + t, 1 - a - t)
    HasDerivWithinAt (fun t : ℝ => quadrantExtension g (a + t, 1 - a))
      (H 0 + (1 - a) * derivWithin H (Iio 0) 0) (Iio 0) 0 := by
  have hmaps : ∀ᶠ t : ℝ in 𝓝[<] 0, (1 - a) * t / (1 + t) ∈ Iio 0 := by
    filter_upwards [one_add_pos_eventually.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with t ht htneg
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (sub_pos.mpr ha₁) htneg) ht
  have hpath := coordinate_path_hasDerivWithinAt g hhom a (1 - a) _ (Iio 0) (Iio 0)
    (hasDerivWithinAt_profile_left g hgconc a ha₀ ha₁) hmaps
  simpa only [show a + (1 - a) = 1 by ring,
    show 1 - a - (1 - a) = 0 by ring, one_mul, zero_mul, add_zero, sub_zero] using hpath

/-- The right first-coordinate derivative is the right transverse derivative
converted by homogeneity; see JR1810.03580v3, Section 2.3. -/
theorem hasDerivWithinAt_first_coordinate_right
    (g : Quadrant → ℝ)
    (hgconc : ∀ (x y : Quadrant) (r s : ℝ≥0), r + s = 1 →
      (r : ℝ) * g x + (s : ℝ) * g y ≤ g (r • x + s • y))
    (hhom : ∀ (r : ℝ≥0) (z : Quadrant), g (r • z) = (r : ℝ) * g z)
    (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) :
    let H : ℝ → ℝ := fun t => quadrantExtension g (a + t, 1 - a - t)
    HasDerivWithinAt (fun t : ℝ => quadrantExtension g (a + t, 1 - a))
      (H 0 + (1 - a) * derivWithin H (Ioi 0) 0) (Ioi 0) 0 := by
  have hmaps : ∀ᶠ t : ℝ in 𝓝[>] 0, (1 - a) * t / (1 + t) ∈ Ioi 0 := by
    filter_upwards [one_add_pos_eventually.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with t ht htpos
    exact div_pos (mul_pos (sub_pos.mpr ha₁) htpos) ht
  have hpath := coordinate_path_hasDerivWithinAt g hhom a (1 - a) _ (Ioi 0) (Ioi 0)
    (hasDerivWithinAt_profile_right g hgconc a ha₀ ha₁) hmaps
  simpa only [show a + (1 - a) = 1 by ring,
    show 1 - a - (1 - a) = 0 by ring, one_mul, zero_mul, add_zero, sub_zero] using hpath

/-- The left second-coordinate derivative uses the right transverse derivative
because normalization reverses sides; see JR1810.03580v3, Section 2.3. -/
theorem hasDerivWithinAt_second_coordinate_left
    (g : Quadrant → ℝ)
    (hgconc : ∀ (x y : Quadrant) (r s : ℝ≥0), r + s = 1 →
      (r : ℝ) * g x + (s : ℝ) * g y ≤ g (r • x + s • y))
    (hhom : ∀ (r : ℝ≥0) (z : Quadrant), g (r • z) = (r : ℝ) * g z)
    (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) :
    let H : ℝ → ℝ := fun t => quadrantExtension g (a + t, 1 - a - t)
    HasDerivWithinAt (fun t : ℝ => quadrantExtension g (a, 1 - a + t))
      (H 0 - a * derivWithin H (Ioi 0) 0) (Iio 0) 0 := by
  have hmaps : ∀ᶠ t : ℝ in 𝓝[<] 0, (-a) * t / (1 + t) ∈ Ioi 0 := by
    filter_upwards [one_add_pos_eventually.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with t ht htneg
    exact div_pos (mul_pos_of_neg_of_neg (neg_neg_of_pos ha₀) htneg) ht
  have hpath := coordinate_path_hasDerivWithinAt g hhom a (-a) _ (Iio 0) (Ioi 0)
    (hasDerivWithinAt_profile_right g hgconc a ha₀ ha₁) hmaps
  simpa only [add_neg_cancel, show 1 - a - -a = 1 by ring,
    one_mul, zero_mul, add_zero, sub_zero, neg_mul, ← sub_eq_add_neg] using hpath

/-- The right second-coordinate derivative uses the left transverse derivative
because normalization reverses sides; see JR1810.03580v3, Section 2.3. -/
theorem hasDerivWithinAt_second_coordinate_right
    (g : Quadrant → ℝ)
    (hgconc : ∀ (x y : Quadrant) (r s : ℝ≥0), r + s = 1 →
      (r : ℝ) * g x + (s : ℝ) * g y ≤ g (r • x + s • y))
    (hhom : ∀ (r : ℝ≥0) (z : Quadrant), g (r • z) = (r : ℝ) * g z)
    (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) :
    let H : ℝ → ℝ := fun t => quadrantExtension g (a + t, 1 - a - t)
    HasDerivWithinAt (fun t : ℝ => quadrantExtension g (a, 1 - a + t))
      (H 0 - a * derivWithin H (Iio 0) 0) (Ioi 0) 0 := by
  have hmaps : ∀ᶠ t : ℝ in 𝓝[>] 0, (-a) * t / (1 + t) ∈ Iio 0 := by
    filter_upwards [one_add_pos_eventually.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with t ht htpos
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos ha₀) htpos) ht
  have hpath := coordinate_path_hasDerivWithinAt g hhom a (-a) _ (Ioi 0) (Iio 0)
    (hasDerivWithinAt_profile_left g hgconc a ha₀ ha₁) hmaps
  simpa only [add_neg_cancel, show 1 - a - -a = 1 by ring,
    one_mul, zero_mul, add_zero, sub_zero, neg_mul, ← sub_eq_add_neg] using hpath

end LPPDifferentiability
