/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Analysis.HomogeneousRescaling
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Asymptotics.Defs
import ProbabilityBasics.Analysis.ConcaveProfileContact
import LPP_Foundations.Analysis.ShapeProfileCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Supporting functionals from the literal shape profile

This file first records the unit-sum normalization forced by homogeneity. The
canonical one-sided profile slopes then produce the actual quadrant supports
and their own-side contact estimates.
-/

public section

open Set
open Filter
open scoped Topology
open scoped NNReal

namespace LPPDifferentiability

/-- A nonzero quadrant point is a positive multiple of its unit-sum profile
point, with the source transverse coordinate in the closed profile interval. -/
theorem quadrant_homogeneous_profile_normalization
    (g : Quadrant → ℝ)
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z)
    (a : ℝ) (z : Quadrant) (hz : z ≠ 0) :
    let n : ℝ := (z.1 : ℝ) + (z.2 : ℝ)
    let rho : ℝ := (1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ)
    let h : ℝ := rho / n
    0 < n ∧ h ∈ Icc (-a) (1 - a) ∧
      g z = n * quadrantExtension g (a + h, 1 - a - h) := by
  let n : ℝ := (z.1 : ℝ) + (z.2 : ℝ)
  let rho : ℝ := (1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ)
  let h : ℝ := rho / n
  change 0 < n ∧ h ∈ Icc (-a) (1 - a) ∧
    g z = n * quadrantExtension g (a + h, 1 - a - h)
  have hz₁ : 0 ≤ (z.1 : ℝ) := NNReal.coe_nonneg _
  have hz₂ : 0 ≤ (z.2 : ℝ) := NNReal.coe_nonneg _
  have hn : 0 < n := by
    have hzcoord : (z.1 : ℝ) ≠ 0 ∨ (z.2 : ℝ) ≠ 0 := by
      by_contra hnot
      push Not at hnot
      apply hz
      apply Prod.ext
      · exact NNReal.coe_injective hnot.1
      · exact NNReal.coe_injective hnot.2
    rcases hzcoord with h₁ | h₂
    · have hp : 0 < (z.1 : ℝ) := lt_of_le_of_ne hz₁ (Ne.symm h₁)
      exact add_pos_of_pos_of_nonneg hp hz₂
    · have hp : 0 < (z.2 : ℝ) := lt_of_le_of_ne hz₂ (Ne.symm h₂)
      exact add_pos_of_nonneg_of_pos hz₁ hp
  have hrho : rho = (z.1 : ℝ) - a * n := by
    dsimp [rho, n]
    ring
  have hcoord : h = (z.1 : ℝ) / n - a := by
    dsimp [h]
    rw [hrho]
    field_simp [ne_of_gt hn]
  have hfrac_nonneg : 0 ≤ (z.1 : ℝ) / n := div_nonneg hz₁ hn.le
  have hfrac_le : (z.1 : ℝ) / n ≤ 1 := by
    apply (div_le_one hn).2
    dsimp [n]
    linarith
  have hh : h ∈ Icc (-a) (1 - a) := by
    change -a ≤ h ∧ h ≤ 1 - a
    rw [hcoord]
    constructor <;> linarith
  have hp₁ : a + h = (z.1 : ℝ) / n := by
    rw [hcoord]
    ring
  have hp₂ : 1 - a - h = (z.2 : ℝ) / n := by
    rw [hcoord]
    field_simp [ne_of_gt hn]
    ring
  let c : ℝ≥0 := ⟨n, hn.le⟩
  have hscale : c • (a + h, 1 - a - h) = quadrantInclusion z := by
    apply Prod.ext
    · change (c : ℝ) * (a + h) = (z.1 : ℝ)
      change n * (a + h) = (z.1 : ℝ)
      rw [hp₁]
      field_simp [ne_of_gt hn]
    · change (c : ℝ) * (1 - a - h) = (z.2 : ℝ)
      change n * (1 - a - h) = (z.2 : ℝ)
      rw [hp₂]
      field_simp [ne_of_gt hn]
  have hvalue : g z = n * quadrantExtension g (a + h, 1 - a - h) := by
    calc
      g z = quadrantExtension g (quadrantInclusion z) :=
        (quadrantExtension_quadrantInclusion g z).symm
      _ = quadrantExtension g (c • (a + h, 1 - a - h)) := by rw [hscale]
      _ = (c : ℝ) * quadrantExtension g (a + h, 1 - a - h) :=
        quadrantExtension_smul g hhom c (a + h, 1 - a - h)
      _ = n * quadrantExtension g (a + h, 1 - a - h) := rfl
  exact ⟨hn, hh, hvalue⟩

/-- Nonnegative homogeneity forces the value at the quadrant origin to vanish. -/
theorem quadrant_smul_homogeneous_at_zero
    (g : Quadrant → ℝ)
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z) :
    g 0 = 0 := by
  simpa only [zero_smul, NNReal.coe_zero, zero_mul] using hhom 0 0

/-- The actual extreme supporting functionals dominate the quadrant shape,
agree with the shape at the chosen direction, and have first-order contact on
their own side of the literal profile. -/
theorem quadrant_supporting_functionals_and_contact
    (g : Quadrant → ℝ)
    (hgconc : ∀ (x y : Quadrant) (r s : ℝ≥0), r + s = 1 →
      (r : ℝ) * g x + (s : ℝ) * g y ≤ g (r • x + s • y))
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z)
    (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) :
    let F : ℝ × ℝ → ℝ := quadrantExtension g
    let H : ℝ → ℝ := fun h => F (a + h, 1 - a - h)
    let level : ℝ × ℝ → ℝ := fun x => x.1 + x.2
    let rho : ℝ × ℝ → ℝ := fun x => (1 - a) * x.1 - a * x.2
    let dl : ℝ := derivWithin H (Iio 0) 0
    let dr : ℝ := derivWithin H (Ioi 0) 0
    let fminus : ℝ × ℝ → ℝ := fun x => H 0 * level x + dl * rho x
    let fplus : ℝ × ℝ → ℝ := fun x => H 0 * level x + dr * rho x
    let favg : ℝ × ℝ → ℝ := fun x => (fminus x + fplus x) / 2
    (∀ z : Quadrant,
      g z ≤ fminus (quadrantInclusion z) ∧
        g z ≤ fplus (quadrantInclusion z)) ∧
      fminus (a, 1 - a) = F (a, 1 - a) ∧
      fplus (a, 1 - a) = F (a, 1 - a) ∧
      favg (a, 1 - a) = F (a, 1 - a) ∧
      ((fun h : ℝ => fminus (a + h, 1 - a - h) - F (a + h, 1 - a - h))
        =o[𝓝[<] (0 : ℝ)] (fun h => |h|)) ∧
      ((fun h : ℝ => fplus (a + h, 1 - a - h) - F (a + h, 1 - a - h))
        =o[𝓝[>] (0 : ℝ)] (fun h => |h|)) := by
  let F : ℝ × ℝ → ℝ := quadrantExtension g
  let H : ℝ → ℝ := fun h => F (a + h, 1 - a - h)
  let level : ℝ × ℝ → ℝ := fun x => x.1 + x.2
  let rho : ℝ × ℝ → ℝ := fun x => (1 - a) * x.1 - a * x.2
  let dl : ℝ := derivWithin H (Iio 0) 0
  let dr : ℝ := derivWithin H (Ioi 0) 0
  let fminus : ℝ × ℝ → ℝ := fun x => H 0 * level x + dl * rho x
  let fplus : ℝ × ℝ → ℝ := fun x => H 0 * level x + dr * rho x
  let favg : ℝ × ℝ → ℝ := fun x => (fminus x + fplus x) / 2
  change
    (∀ z : Quadrant,
      g z ≤ fminus (quadrantInclusion z) ∧
        g z ≤ fplus (quadrantInclusion z)) ∧
      fminus (a, 1 - a) = F (a, 1 - a) ∧
      fplus (a, 1 - a) = F (a, 1 - a) ∧
      favg (a, 1 - a) = F (a, 1 - a) ∧
      ((fun h : ℝ => fminus (a + h, 1 - a - h) - F (a + h, 1 - a - h))
        =o[𝓝[<] (0 : ℝ)] (fun h => |h|)) ∧
      ((fun h : ℝ => fplus (a + h, 1 - a - h) - F (a + h, 1 - a - h))
        =o[𝓝[>] (0 : ℝ)] (fun h => |h|))
  have hprofile : ConcaveOn ℝ (Icc (-a) (1 - a)) H :=
    concaveOn_quadrantExtension_profile g hgconc a
  have hcontact := ConcaveOn.supporting_lines_and_one_sided_contact
    hprofile (by linarith [ha₀]) (by linarith [ha₁])
  have hzero : g (0 : Quadrant) = 0 :=
    quadrant_smul_homogeneous_at_zero g hhom
  have hsupp : ∀ z : Quadrant,
      g z ≤ fminus (quadrantInclusion z) ∧
        g z ≤ fplus (quadrantInclusion z) := by
    intro z
    by_cases hz : z = 0
    · subst z
      rw [hzero]
      simp [fminus, fplus, level, rho, quadrantInclusion]
    · let n : ℝ := (z.1 : ℝ) + (z.2 : ℝ)
      let transverse : ℝ := (1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ)
      let h : ℝ := transverse / n
      have hgeom := quadrant_homogeneous_profile_normalization g hhom a z hz
      rcases hgeom with ⟨hn, hh, hvalue⟩
      change 0 < n at hn
      change h ∈ Icc (-a) (1 - a) at hh
      change g z = n * H h at hvalue
      have htransverse : n * h = transverse := by
        dsimp [h]
        exact mul_div_cancel₀ _ (ne_of_gt hn)
      have hminusProfile : H h ≤ H 0 + dl * h := hcontact.1 h hh
      have hplusProfile : H h ≤ H 0 + dr * h := hcontact.2.1 h hh
      have hminusBound : n * H h ≤ H 0 * n + dl * transverse := by
        calc
          n * H h ≤ n * (H 0 + dl * h) :=
            mul_le_mul_of_nonneg_left hminusProfile hn.le
          _ = n * H 0 + dl * (n * h) := by ring
          _ = H 0 * n + dl * transverse := by rw [htransverse]; ring
      have hplusBound : n * H h ≤ H 0 * n + dr * transverse := by
        calc
          n * H h ≤ n * (H 0 + dr * h) :=
            mul_le_mul_of_nonneg_left hplusProfile hn.le
          _ = n * H 0 + dr * (n * h) := by ring
          _ = H 0 * n + dr * transverse := by rw [htransverse]; ring
      have hminusAt :
          fminus (quadrantInclusion z) = H 0 * n + dl * transverse := by
        change H 0 * n + dl * transverse = H 0 * n + dl * transverse
        rfl
      have hplusAt :
          fplus (quadrantInclusion z) = H 0 * n + dr * transverse := by
        change H 0 * n + dr * transverse = H 0 * n + dr * transverse
        rfl
      constructor
      · calc
          g z = n * H h := hvalue
          _ ≤ H 0 * n + dl * transverse := hminusBound
          _ = fminus (quadrantInclusion z) := hminusAt.symm
      · calc
          g z = n * H h := hvalue
          _ ≤ H 0 * n + dr * transverse := hplusBound
          _ = fplus (quadrantInclusion z) := hplusAt.symm
  have hHzero : H 0 = F (a, 1 - a) := by
    simp only [H, add_zero, sub_zero]
  have hminusDirection : fminus (a, 1 - a) = F (a, 1 - a) := by
    change H 0 * (a + (1 - a)) + dl * ((1 - a) * a - a * (1 - a)) = _
    rw [hHzero]
    ring
  have hplusDirection : fplus (a, 1 - a) = F (a, 1 - a) := by
    change H 0 * (a + (1 - a)) + dr * ((1 - a) * a - a * (1 - a)) = _
    rw [hHzero]
    ring
  have havgDirection : favg (a, 1 - a) = F (a, 1 - a) := by
    change (fminus (a, 1 - a) + fplus (a, 1 - a)) / 2 = _
    rw [hminusDirection, hplusDirection]
    ring
  have hminusContact :
      (fun h : ℝ => fminus (a + h, 1 - a - h) - F (a + h, 1 - a - h))
        =o[𝓝[<] (0 : ℝ)] (fun h => |h|) := by
    refine hcontact.2.2.1.congr (fun h => ?_) (fun _ => rfl)
    change H 0 + dl * h - H h =
      H 0 * ((a + h) + (1 - a - h)) +
        dl * ((1 - a) * (a + h) - a * (1 - a - h)) - H h
    ring
  have hplusContact :
      (fun h : ℝ => fplus (a + h, 1 - a - h) - F (a + h, 1 - a - h))
        =o[𝓝[>] (0 : ℝ)] (fun h => |h|) := by
    refine hcontact.2.2.2.congr (fun h => ?_) (fun _ => rfl)
    change H 0 + dr * h - H h =
      H 0 * ((a + h) + (1 - a - h)) +
        dr * ((1 - a) * (a + h) - a * (1 - a - h)) - H h
    ring
  exact ⟨hsupp, hminusDirection, hplusDirection, havgDirection,
    hminusContact, hplusContact⟩

/-- The actual half-gap is nonnegative, and the two supports differ from
their average by exactly that half-gap times the source transverse coordinate. -/
theorem quadrant_supporting_functionals_half_gap_algebra
    (g : Quadrant → ℝ)
    (hgconc : ∀ (x y : Quadrant) (r s : ℝ≥0), r + s = 1 →
      (r : ℝ) * g x + (s : ℝ) * g y ≤ g (r • x + s • y))
    (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) :
    let F : ℝ × ℝ → ℝ := quadrantExtension g
    let H : ℝ → ℝ := fun h => F (a + h, 1 - a - h)
    let level : ℝ × ℝ → ℝ := fun x => x.1 + x.2
    let rho : ℝ × ℝ → ℝ := fun x => (1 - a) * x.1 - a * x.2
    let dl : ℝ := derivWithin H (Iio 0) 0
    let dr : ℝ := derivWithin H (Ioi 0) 0
    let fminus : ℝ × ℝ → ℝ := fun x => H 0 * level x + dl * rho x
    let fplus : ℝ × ℝ → ℝ := fun x => H 0 * level x + dr * rho x
    let favg : ℝ × ℝ → ℝ := fun x => (fminus x + fplus x) / 2
    let cgap : ℝ := (dl - dr) / 2
    0 ≤ cgap ∧
      (∀ x : ℝ × ℝ, fminus x = favg x + cgap * rho x) ∧
      (∀ x : ℝ × ℝ, fplus x = favg x - cgap * rho x) := by
  let F : ℝ × ℝ → ℝ := quadrantExtension g
  let H : ℝ → ℝ := fun h => F (a + h, 1 - a - h)
  let level : ℝ × ℝ → ℝ := fun x => x.1 + x.2
  let rho : ℝ × ℝ → ℝ := fun x => (1 - a) * x.1 - a * x.2
  let dl : ℝ := derivWithin H (Iio 0) 0
  let dr : ℝ := derivWithin H (Ioi 0) 0
  let fminus : ℝ × ℝ → ℝ := fun x => H 0 * level x + dl * rho x
  let fplus : ℝ × ℝ → ℝ := fun x => H 0 * level x + dr * rho x
  let favg : ℝ × ℝ → ℝ := fun x => (fminus x + fplus x) / 2
  let cgap : ℝ := (dl - dr) / 2
  change 0 ≤ cgap ∧
    (∀ x : ℝ × ℝ, fminus x = favg x + cgap * rho x) ∧
    (∀ x : ℝ × ℝ, fplus x = favg x - cgap * rho x)
  have horder : dr ≤ dl := profile_rightDeriv_le_leftDeriv g hgconc a ha₀ ha₁
  have hgap : 0 ≤ cgap := by
    dsimp [cgap]
    linarith
  refine ⟨hgap, ?_, ?_⟩
  · intro x
    change H 0 * level x + dl * rho x =
      (H 0 * level x + dl * rho x + (H 0 * level x + dr * rho x)) / 2 +
        ((dl - dr) / 2) * rho x
    ring
  · intro x
    change H 0 * level x + dr * rho x =
      (H 0 * level x + dl * rho x + (H 0 * level x + dr * rho x)) / 2 -
        ((dl - dr) / 2) * rho x
    ring

end LPPDifferentiability
