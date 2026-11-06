/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Interiority after two natural attachment displacements

Two natural attachments of the same length `m` can be removed from a point deep inside the cone
without leaving the lattice quadrant. The middle displacement that remains lies in a slightly
smaller cone, and its length is `n - 2 * m`.
-/

public section

namespace LPPDifferentiability

/-- A natural attachment of length `m` has signed transverse coordinate of
absolute value at most `m`. -/
theorem attachment_transverse_bound
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (e : ℕ × ℕ) (m : ℕ) (he : e.1 + e.2 = m) :
    |(1 - a) * (e.1 : ℝ) - a * (e.2 : ℝ)| ≤ (m : ℝ) := by
  have he1 : 0 ≤ (e.1 : ℝ) := Nat.cast_nonneg _
  have he2 : 0 ≤ (e.2 : ℝ) := Nat.cast_nonneg _
  have hm : (e.1 : ℝ) + (e.2 : ℝ) = (m : ℝ) := by exact_mod_cast he
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  have he1le : (e.1 : ℝ) ≤ (m : ℝ) := by rw [← hm]; linarith
  have he2le : (e.2 : ℝ) ≤ (m : ℝ) := by rw [← hm]; linarith
  have hcoefA : 0 ≤ a := le_of_lt ha0
  have hcoefB : 0 ≤ 1 - a := by linarith
  have hcoefAone : a ≤ 1 := le_of_lt ha1
  have hcoefBone : 1 - a ≤ 1 := by linarith
  have hfirst : 0 ≤ (1 - a) * (e.1 : ℝ) := mul_nonneg hcoefB he1
  have hsecond : 0 ≤ a * (e.2 : ℝ) := mul_nonneg hcoefA he2
  have hfirstUpper := mul_le_mul_of_nonneg_left he1le hcoefB
  have hsecondUpper := mul_le_mul_of_nonneg_left he2le hcoefA
  have hfirstScale := mul_le_mul_of_nonneg_right hcoefBone hm0
  have hsecondScale := mul_le_mul_of_nonneg_right hcoefAone hm0
  apply abs_le.mpr
  constructor
  · nlinarith
  · nlinarith

/-- For a displacement in the cone, subtracting two natural
attachments is nontruncated and leaves a displacement in the smaller cone.
The length and transverse bounds are proved for the resulting natural pair. -/
theorem attachment_interiority
    (a theta s D : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (htheta0 : 0 < theta) (htheta : theta < min a (1 - a))
    (hs : 0 < s) (hD : 1 ≤ D)
    (n : ℕ) (d e₁ e₂ : ℕ × ℕ) (m : ℕ)
    (hlevel : d.1 + d.2 = n)
    (hscaleLo : s ≤ (n : ℝ)) (hscaleHi : (n : ℝ) ≤ D * s)
    (hinterior : |(1 - a) * (d.1 : ℝ) - a * (d.2 : ℝ)| ≤
      (min a (1 - a) - theta) * (n : ℝ))
    (he₁ : e₁.1 + e₁.2 = m) (he₂ : e₂.1 + e₂.2 = m)
    (hcut1 : 2 * (m : ℝ) ≤ s / 4)
    (hcut2 : (theta / 2) * s ≥
      2 * (m : ℝ) * (1 + min a (1 - a) - theta / 2)) :
    let mid : ℕ × ℕ := d - e₁ - e₂
    (|(1 - a) * (e₁.1 : ℝ) - a * (e₁.2 : ℝ)| ≤ (m : ℝ) ∧
      |(1 - a) * (e₂.1 : ℝ) - a * (e₂.2 : ℝ)| ≤ (m : ℝ)) ∧
    (e₁.1 + e₂.1 ≤ d.1 ∧ e₁.2 + e₂.2 ≤ d.2) ∧
    d = mid + e₁ + e₂ ∧
    mid.1 + mid.2 = n - 2 * m ∧
    (s / 2 ≤ (mid.1 : ℝ) + (mid.2 : ℝ) ∧
      (mid.1 : ℝ) + (mid.2 : ℝ) ≤ D * s) ∧
    0 < (mid.1 : ℝ) + (mid.2 : ℝ) ∧
    |(1 - a) * (mid.1 : ℝ) - a * (mid.2 : ℝ)| ≤
      (min a (1 - a) - theta / 2) * ((mid.1 : ℝ) + (mid.2 : ℝ)) := by
  intro mid
  let theta0 : ℝ := min a (1 - a)
  let rho : (ℕ × ℕ) → ℝ := fun x => (1 - a) * (x.1 : ℝ) - a * (x.2 : ℝ)
  have hncast : (d.1 : ℝ) + (d.2 : ℝ) = (n : ℝ) := by exact_mod_cast hlevel
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  have hminA : theta0 ≤ a := by dsimp [theta0]; exact min_le_left _ _
  have hminB : theta0 ≤ 1 - a := by dsimp [theta0]; exact min_le_right _ _
  have hgapHalf : 0 < theta0 - theta / 2 := by linarith
  have hfactorMargin : 0 ≤ (m : ℝ) * (theta0 - theta / 2) :=
    mul_nonneg hm0 hgapHalf.le
  have hthetaS : 4 * (m : ℝ) ≤ theta * s := by
    nlinarith [hcut2, hfactorMargin]
  have hcoord1 : theta * (n : ℝ) ≤ (d.1 : ℝ) := by
    have hrhoIn : |rho d| ≤ (theta0 - theta) * (n : ℝ) := by
      simpa [rho, theta0] using hinterior
    have hrho := (abs_le.mp hrhoIn).1
    have hrhoEq : rho d = (d.1 : ℝ) - a * (n : ℝ) := by
      dsimp [rho]
      rw [← hncast]
      ring
    rw [hrhoEq] at hrho
    have hgap : 0 ≤ (a - theta0) * (n : ℝ) :=
      mul_nonneg (sub_nonneg.mpr hminA) hn0
    nlinarith [hrho, hgap]
  have hcoord2 : theta * (n : ℝ) ≤ (d.2 : ℝ) := by
    have hrhoIn : |rho d| ≤ (theta0 - theta) * (n : ℝ) := by
      simpa [rho, theta0] using hinterior
    have hrho := (abs_le.mp hrhoIn).2
    have hrhoEq : rho d = (1 - a) * (n : ℝ) - (d.2 : ℝ) := by
      dsimp [rho]
      rw [← hncast]
      ring
    rw [hrhoEq] at hrho
    have hgap : 0 ≤ (1 - a - theta0) * (n : ℝ) :=
      mul_nonneg (sub_nonneg.mpr hminB) hn0
    nlinarith [hrho, hgap]
  have hthetaN : theta * s ≤ theta * (n : ℝ) :=
    mul_le_mul_of_nonneg_left hscaleLo htheta0.le
  have hcoord1big : 4 * (m : ℝ) ≤ (d.1 : ℝ) := by linarith
  have hcoord2big : 4 * (m : ℝ) ≤ (d.2 : ℝ) := by linarith
  have hcoord1four : 4 * m ≤ d.1 := by exact_mod_cast hcoord1big
  have hcoord2four : 4 * m ≤ d.2 := by exact_mod_cast hcoord2big
  have hcoord1double : 2 * m ≤ d.1 := by omega
  have hcoord2double : 2 * m ≤ d.2 := by omega
  have hsum1le : e₁.1 + e₂.1 ≤ 2 * m := by omega
  have hsum2le : e₁.2 + e₂.2 ≤ 2 * m := by omega
  have hnontrunc1 : e₁.1 + e₂.1 ≤ d.1 := hsum1le.trans hcoord1double
  have hnontrunc2 : e₁.2 + e₂.2 ≤ d.2 := hsum2le.trans hcoord2double
  have hdecomp : d = mid + e₁ + e₂ := by
    apply Prod.ext <;> simp [mid] <;> omega
  have hcoord1nat : d.1 = mid.1 + e₁.1 + e₂.1 := by
    simpa using congrArg Prod.fst hdecomp
  have hcoord2nat : d.2 = mid.2 + e₁.2 + e₂.2 := by
    simpa using congrArg Prod.snd hdecomp
  have hcoord1real : (d.1 : ℝ) = (mid.1 : ℝ) + (e₁.1 : ℝ) + (e₂.1 : ℝ) := by
    exact_mod_cast hcoord1nat
  have hcoord2real : (d.2 : ℝ) = (mid.2 : ℝ) + (e₁.2 : ℝ) + (e₂.2 : ℝ) := by
    exact_mod_cast hcoord2nat
  have hmidlenAdd : mid.1 + mid.2 + 2 * m = n := by omega
  have hmidlen : mid.1 + mid.2 = n - 2 * m := by omega
  have hmidlenAddReal : (mid.1 : ℝ) + (mid.2 : ℝ) + 2 * (m : ℝ) = (n : ℝ) := by
    exact_mod_cast hmidlenAdd
  have hmidlenReal : (mid.1 : ℝ) + (mid.2 : ℝ) =
      (n : ℝ) - 2 * (m : ℝ) := by
    linarith only [hmidlenAddReal]
  have hDscale : s ≤ D * s := by
    calc
      s = 1 * s := by ring
      _ ≤ D * s := mul_le_mul_of_nonneg_right hD hs.le
  have hmidlenLeN : (mid.1 : ℝ) + (mid.2 : ℝ) ≤ (n : ℝ) := by
    have hmidlenLeNat : mid.1 + mid.2 ≤ n := by omega
    exact_mod_cast hmidlenLeNat
  have hmidlenLeDs : (mid.1 : ℝ) + (mid.2 : ℝ) ≤ D * s := by
    calc
      (mid.1 : ℝ) + (mid.2 : ℝ) ≤ max s (n : ℝ) :=
        hmidlenLeN.trans (le_max_right _ _)
      _ ≤ D * s := max_le hDscale hscaleHi
  have hmidlenGe : s / 2 ≤ (mid.1 : ℝ) + (mid.2 : ℝ) := by
    rw [hmidlenReal]
    linarith only [hscaleLo, hcut1, hs]
  have hmidlenPos : 0 < (mid.1 : ℝ) + (mid.2 : ℝ) := by
    linarith only [hmidlenGe, hs]
  have he₁rho : |rho e₁| ≤ (m : ℝ) := by
    exact attachment_transverse_bound a ha0 ha1 e₁ m he₁
  have he₂rho : |rho e₂| ≤ (m : ℝ) := by
    exact attachment_transverse_bound a ha0 ha1 e₂ m he₂
  have hrhoDecomp : rho d = rho mid + rho e₁ + rho e₂ := by
    dsimp [rho]
    rw [hcoord1real, hcoord2real]
    ring
  have hmidrhoBound : |rho mid| ≤ (theta0 - theta) * (n : ℝ) + 2 * (m : ℝ) := by
    have hrhoD : |rho d| ≤ (theta0 - theta) * (n : ℝ) := by
      simpa [rho, theta0] using hinterior
    have hrhoMidEq : rho mid = rho d - rho e₁ - rho e₂ := by
      linarith only [hrhoDecomp]
    rw [hrhoMidEq]
    calc
      |rho d - rho e₁ - rho e₂| ≤ |rho d - rho e₁| + |rho e₂| := abs_sub _ _
      _ ≤ (|rho d| + |rho e₁|) + |rho e₂| := by
        linarith only [abs_sub (rho d) (rho e₁)]
      _ ≤ (theta0 - theta) * (n : ℝ) + 2 * (m : ℝ) := by
        linarith only [hrhoD, he₁rho, he₂rho]
  have hcutN : 2 * (m : ℝ) * (1 + theta0 - theta / 2) ≤
      (theta / 2) * (n : ℝ) := by
    have hscale : (theta / 2) * s ≤ (theta / 2) * (n : ℝ) :=
      mul_le_mul_of_nonneg_left hscaleLo (by positivity)
    linarith only [hcut2, hscale]
  have hcutRearranged : (theta0 - theta) * (n : ℝ) + 2 * (m : ℝ) ≤
      (theta0 - theta / 2) * ((n : ℝ) - 2 * (m : ℝ)) := by
    nlinarith only [hcutN]
  have hmidrho : |rho mid| ≤
      (theta0 - theta / 2) * ((mid.1 : ℝ) + (mid.2 : ℝ)) := by
    calc
      |rho mid| ≤ (theta0 - theta) * (n : ℝ) + 2 * (m : ℝ) := hmidrhoBound
      _ ≤ (theta0 - theta / 2) * ((mid.1 : ℝ) + (mid.2 : ℝ)) := by
        rw [hmidlenReal]
        exact hcutRearranged
  constructor
  · exact ⟨by simpa [rho] using he₁rho, by simpa [rho] using he₂rho⟩
  constructor
  · exact ⟨hnontrunc1, hnontrunc2⟩
  constructor
  · exact hdecomp
  constructor
  · exact hmidlen
  constructor
  · exact ⟨hmidlenGe, hmidlenLeDs⟩
  constructor
  · exact hmidlenPos
  · simpa [rho, theta0] using hmidrho

end LPPDifferentiability
