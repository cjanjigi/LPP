/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Analysis.AttachmentInteriority
public import LPP_Foundations.Analysis.HomogeneousShapeLipschitz
import Mathlib.Tactic

/-!
# Shape comparison after natural attachments

For a shape function that is concave and homogeneous on the quadrant, removing two natural
attachments of the same length `m` changes the shape value by at most `2 * L * m`. The constant `L`
is chosen before the attachment data.
-/

public section

open scoped NNReal

namespace LPPDifferentiability

/-- One shape constant, chosen before all attachment data, controls the exact
natural middle displacement. Shape values may have either sign. -/
theorem attachment_shape_comparison
    (g : Quadrant → ℝ) (hgcont : Continuous g)
    (hgconc : ∀ (x y : Quadrant) (r t : ℝ≥0), r + t = 1 →
      (r : ℝ) * g x + (t : ℝ) * g y ≤ g (r • x + t • y))
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z)
    (a theta : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (htheta0 : 0 < theta) (htheta : theta < min a (1 - a)) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ (s D : ℝ), 0 < s → 1 ≤ D →
      ∀ (n : ℕ) (d e₁ e₂ : ℕ × ℕ) (m : ℕ),
      d.1 + d.2 = n → s ≤ (n : ℝ) → (n : ℝ) ≤ D * s →
      |(1 - a) * (d.1 : ℝ) - a * (d.2 : ℝ)| ≤
        (min a (1 - a) - theta) * (n : ℝ) →
      e₁.1 + e₁.2 = m → e₂.1 + e₂.2 = m →
      2 * (m : ℝ) ≤ s / 4 →
      (theta / 2) * s ≥ 2 * (m : ℝ) * (1 + min a (1 - a) - theta / 2) →
      let mid : ℕ × ℕ := d - e₁ - e₂
      (|(d.1 : ℝ) - (mid.1 : ℝ)| + |(d.2 : ℝ) - (mid.2 : ℝ)| = 2 * (m : ℝ)) ∧
      |g ((mid.1 : ℝ≥0), (mid.2 : ℝ≥0)) - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
        2 * L * (m : ℝ) ∧
      g ((mid.1 : ℝ≥0), (mid.2 : ℝ≥0)) ≥
        g ((d.1 : ℝ≥0), (d.2 : ℝ≥0)) - 2 * L * (m : ℝ) := by
  have hhalf0 : 0 < theta / 2 := by linarith
  have hhalf : theta / 2 < min a (1 - a) := by linarith
  obtain ⟨L, hL, hLip⟩ := quadrant_homogeneous_shape_lipschitz_on_adapted_cone
    g hgcont hgconc hhom a (theta / 2) ha0 ha1 hhalf0 hhalf
  refine ⟨L, hL, ?_⟩
  intro s D hs hD n d e₁ e₂ m hlevel hlo hhi hcone he₁ he₂ hcut₁ hcut₂ mid
  obtain ⟨_, _, hdecomp, _, _, _, hmidcone⟩ :=
    attachment_interiority a theta s D ha0 ha1 htheta0 htheta hs hD
      n d e₁ e₂ m hlevel hlo hhi hcone he₁ he₂ hcut₁ hcut₂
  have hdecompMid : d = mid + e₁ + e₂ := hdecomp
  have hmidconeMid : |(1 - a) * (mid.1 : ℝ) - a * (mid.2 : ℝ)| ≤
      (min a (1 - a) - theta / 2) * ((mid.1 : ℝ) + (mid.2 : ℝ)) := hmidcone
  have hfirst : d.1 = mid.1 + e₁.1 + e₂.1 := by
    simpa using congrArg Prod.fst hdecompMid
  have hsecond : d.2 = mid.2 + e₁.2 + e₂.2 := by
    simpa using congrArg Prod.snd hdecompMid
  have hfirstR : (d.1 : ℝ) = (mid.1 : ℝ) + (e₁.1 : ℝ) + (e₂.1 : ℝ) := by
    exact_mod_cast hfirst
  have hsecondR : (d.2 : ℝ) = (mid.2 : ℝ) + (e₁.2 : ℝ) + (e₂.2 : ℝ) := by
    exact_mod_cast hsecond
  have he₁R : (e₁.1 : ℝ) + (e₁.2 : ℝ) = (m : ℝ) := by exact_mod_cast he₁
  have he₂R : (e₂.1 : ℝ) + (e₂.2 : ℝ) = (m : ℝ) := by exact_mod_cast he₂
  have hdist : |(d.1 : ℝ) - (mid.1 : ℝ)| + |(d.2 : ℝ) - (mid.2 : ℝ)| =
      2 * (m : ℝ) := by
    have he₁₁ : 0 ≤ (e₁.1 : ℝ) := Nat.cast_nonneg _
    have he₂₁ : 0 ≤ (e₂.1 : ℝ) := Nat.cast_nonneg _
    have he₁₂ : 0 ≤ (e₁.2 : ℝ) := Nat.cast_nonneg _
    have he₂₂ : 0 ≤ (e₂.2 : ℝ) := Nat.cast_nonneg _
    have hpos₁ : 0 ≤ (d.1 : ℝ) - (mid.1 : ℝ) := by
      linarith only [hfirstR, he₁₁, he₂₁]
    have hpos₂ : 0 ≤ (d.2 : ℝ) - (mid.2 : ℝ) := by
      linarith only [hsecondR, he₁₂, he₂₂]
    rw [abs_of_nonneg hpos₁, abs_of_nonneg hpos₂]
    linarith only [hfirstR, hsecondR, he₁R, he₂R]
  have hlevelR : (d.1 : ℝ) + (d.2 : ℝ) = (n : ℝ) := by exact_mod_cast hlevel
  have hdcone : |(1 - a) * (d.1 : ℝ) - a * (d.2 : ℝ)| ≤
      (min a (1 - a) - theta / 2) * ((d.1 : ℝ) + (d.2 : ℝ)) := by
    rw [hlevelR]
    have hmargin : 0 ≤ (theta / 2) * (n : ℝ) :=
      mul_nonneg hhalf0.le (Nat.cast_nonneg n)
    nlinarith only [hcone, hmargin]
  have hbound := hLip ((mid.1 : ℝ≥0), (mid.2 : ℝ≥0))
    ((d.1 : ℝ≥0), (d.2 : ℝ≥0)) ⟨by simpa only [NNReal.coe_natCast] using hmidconeMid,
      by simpa only [NNReal.coe_natCast] using hdcone⟩
  have habs : |g ((mid.1 : ℝ≥0), (mid.2 : ℝ≥0)) -
      g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤ 2 * L * (m : ℝ) := by
    have hdist' : |(mid.1 : ℝ) - (d.1 : ℝ)| + |(mid.2 : ℝ) - (d.2 : ℝ)| =
        2 * (m : ℝ) := by simpa only [abs_sub_comm] using hdist
    simpa only [NNReal.coe_natCast, hdist', mul_left_comm, mul_assoc] using hbound
  exact ⟨hdist, habs, by linarith only [(abs_le.mp habs).1]⟩

end LPPDifferentiability
