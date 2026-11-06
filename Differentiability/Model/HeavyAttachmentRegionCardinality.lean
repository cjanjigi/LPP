/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.FiniteLevelStripCardinality
public import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-! Cardinality of the signed region used in heavy attachments. -/
public section

namespace LPPDifferentiability

/-- The source region is finite and satisfies its cardinality bound. -/
theorem exists_finset_heavy_attachment_region
    (a D s kappa rho1 rho2 : ℝ) (I : ℤ) (K : ℕ)
    (hD : 1 ≤ D) (hs : 4 ≤ s) (hkappa : 0 < kappa)
    (hkappaCap : kappa ≤ (1 / 16 : ℝ))
    (hrange : rho1 ≤ rho2) (hwidth : rho2-rho1 ≤ D*s)
    (hcut : 2*(K:ℝ)+5 ≤ (Nat.ceil (kappa*s) : ℝ)) :
    ∃ Q : Finset Lattice,
      (∀ z, z ∈ Q ↔
        I ≤ z.1+z.2 ∧ z.1+z.2 ≤ I+(Nat.ceil (kappa*s) : ℤ) ∧
        rho1-(Nat.ceil (kappa*s) : ℝ)-(K:ℝ)-2 ≤
          (1-a)*(z.1:ℝ)-a*(z.2:ℝ) ∧
        (1-a)*(z.1:ℝ)-a*(z.2:ℝ) ≤
          rho2+(Nat.ceil (kappa*s) : ℝ)+(K:ℝ)+2) ∧
      (Q.card : ℝ) ≤ 4*D*s^2 := by
  classical
  let m : ℕ := Nat.ceil (kappa*s)
  let lo : ℤ → ℝ := fun _ => rho1-(m:ℝ)-(K:ℝ)-2
  let hi : ℤ → ℝ := fun _ => rho2+(m:ℝ)+(K:ℝ)+2
  let W : ℝ := D*s+2*(m:ℝ)+2*(K:ℝ)+4
  have hs0 : 0 ≤ s := by linarith
  have hD0 : 0 ≤ D := by linarith
  have hK0 : 0 ≤ (K:ℝ) := by positivity
  have hmceil : (m:ℝ) ≤ kappa*s+1 := by
    dsimp only [m]
    exact (Nat.ceil_lt_add_one (mul_nonneg hkappa.le hs0)).le
  have hks : kappa*s ≤ s/16 := by
    have hmul := mul_le_mul_of_nonneg_right hkappaCap hs0
    nlinarith only [hmul]
  have hmHalf : (m:ℝ) ≤ s/2 := by
    nlinarith only [hmceil, hks, hs]
  have hmPlus : (m:ℝ)+1 ≤ s := by
    nlinarith only [hmceil, hks, hs]
  have hcutm : 2*(K:ℝ)+5 ≤ (m:ℝ) := by
    dsimp only [m]
    exact hcut
  have hsDs : s ≤ D*s := by
    have h := mul_le_mul_of_nonneg_right hD hs0
    simpa only [one_mul] using h
  have hfactor : W+1 ≤ (5/2)*D*s := by
    dsimp only [W]
    calc
      D*s+2*(m:ℝ)+2*(K:ℝ)+4+1 ≤ D*s+3*(m:ℝ) := by
        nlinarith only [hcutm]
      _ ≤ D*s+(3/2)*s := by
        have h := mul_le_mul_of_nonneg_left hmHalf
          (by norm_num : 0 ≤ (3:ℝ))
        nlinarith only [h]
      _ ≤ (5/2)*D*s := by
        have h := mul_le_mul_of_nonneg_left hsDs
          (by norm_num : 0 ≤ (3/2:ℝ))
        linarith only [h]
  have hW : 0 ≤ W := by
    dsimp only [W]
    positivity
  have hwindow (k : ℤ) (hklo : I ≤ k) (hkhi : k ≤ I+(m:ℤ)) :
      lo k ≤ hi k := by
    dsimp only [lo, hi]
    linarith
  have htranswidth (k : ℤ) (hklo : I ≤ k) (hkhi : k ≤ I+(m:ℤ)) :
      hi k-lo k ≤ W := by
    dsimp only [lo, hi, W]
    linarith only [hwidth]
  obtain ⟨Q, hQmem, hQcard⟩ :=
    exists_finset_signed_level_window a W I m lo hi hW hwindow htranswidth
  have hsmall : ((m+1:ℕ):ℝ) ≤ s := by
    simpa only [Nat.cast_add, Nat.cast_one] using hmPlus
  have hWplus : 0 ≤ W+1 := by linarith [hW]
  have hcardBound : ((m+1:ℕ):ℝ)*(W+1) ≤ 4*D*s^2 := by
    calc
      ((m+1:ℕ):ℝ)*(W+1) ≤ s*((5/2)*D*s) :=
        mul_le_mul hsmall hfactor hWplus hs0
      _ = (5/2)*D*s^2 := by ring
      _ ≤ 4*D*s^2 := by
        have hcoeff : (5/2:ℝ) ≤ 4 := by norm_num
        have hcoeffD : (5/2)*D ≤ 4*D :=
          mul_le_mul_of_nonneg_right hcoeff hD0
        have hs2 : 0 ≤ s^2 := by positivity
        exact mul_le_mul_of_nonneg_right hcoeffD hs2
  refine ⟨Q, ?_, ?_⟩
  · intro z
    simpa only [m, lo, hi] using hQmem z
  · exact hQcard.trans hcardBound

end LPPDifferentiability

end
