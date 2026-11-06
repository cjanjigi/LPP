/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.FiniteLevelStripCardinality
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-! The finite working region used in the staircase and heavy-vertex arguments. -/
public section

namespace LPPDifferentiability

/-- The working region is finite, with its exact membership condition and an explicit
fourth-power cardinality bound. The direction parameter `a` is unrestricted. -/
theorem exists_finset_heavy_working_region
    (a A R c₁ s : ℝ) (ell : ℕ)
    (hA : 0 < A) (hR : 0 < R) (hc₁ : 0 ≤ c₁)
    (hs : 1 ≤ s) (hell : 1 ≤ ell) (hells : (ell : ℝ) ≤ s^3) :
    ∃ Q : Finset Lattice,
      (∀ z, z ∈ Q ↔
        |((z.1 + z.2 : ℤ) : ℝ)| ≤ (A + 5) * (ell : ℝ) ∧
          |(1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ)| ≤ (R + 2 * c₁ + 10) * s) ∧
      (Q.card : ℝ) ≤ (2 * A + 11) * (2 * R + 4 * c₁ + 21) * s^4 := by
  classical
  let C : ℝ := A + 5
  let D : ℝ := R + 2 * c₁ + 10
  let M : ℝ := C * (ell : ℝ)
  let H : ℝ := D * s
  have hC : 0 < C := by
    dsimp only [C]
    linarith
  have hD : 0 < D := by
    dsimp only [D]
    linarith
  have hellPos : 0 < (ell : ℝ) := by
    exact_mod_cast hell
  have hM : 0 < M := by
    dsimp only [M]
    positivity
  have hH : 0 < H := by
    dsimp only [H]
    positivity
  let F : ℤ := Int.floor M
  let I : ℤ := -F
  let m : ℕ := 2 * F.toNat
  have hFnonneg : 0 ≤ F := by
    dsimp only [F]
    exact Int.floor_nonneg.2 hM.le
  have hFtoNat : (F.toNat : ℤ) = F := Int.toNat_of_nonneg hFnonneg
  have hmCast : (m : ℤ) = 2 * F := by
    dsimp only [m]
    push_cast
    exact congrArg (fun n : ℤ => 2 * n) hFtoNat
  have hIceil : I = Int.ceil (-M) := by
    dsimp only [I, F]
    rw [Int.ceil_neg]
  have hIupper : I + (m : ℤ) = F := by
    dsimp only [I]
    rw [hmCast]
    ring
  have hlevel (z : Lattice) :
      (I ≤ z.1 + z.2 ∧ z.1 + z.2 ≤ I + (m : ℤ)) ↔
        |((z.1 + z.2 : ℤ) : ℝ)| ≤ M := by
    rw [hIupper, hIceil]
    simp only [F, Int.ceil_le, Int.le_floor, abs_le]
  have hcount : ((m + 1 : ℕ) : ℝ) ≤ 2 * M + 1 := by
    have hmReal : (m : ℝ) = 2 * (F : ℝ) := by
      exact_mod_cast hmCast
    have hFle : (F : ℝ) ≤ M := by
      dsimp only [F]
      exact Int.floor_le M
    calc
      ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by norm_cast
      _ = 2 * (F : ℝ) + 1 := by rw [hmReal]
      _ ≤ 2 * M + 1 := by nlinarith only [hFle]
  have hCnonneg : 0 ≤ C := hC.le
  have hMscale : M ≤ C * s^3 := by
    dsimp only [M]
    exact mul_le_mul_of_nonneg_left hells hCnonneg
  have hs3 : 1 ≤ s^3 := one_le_pow₀ hs
  have hlevelCount : 2 * M + 1 ≤ (2 * C + 1) * s^3 := by
    calc
      2 * M + 1 ≤ 2 * (C * s^3) + 1 := by nlinarith only [hMscale]
      _ ≤ (2 * C + 1) * s^3 := by nlinarith only [hs3]
  have hHcount : 2 * H + 1 ≤ (2 * D + 1) * s := by
    dsimp only [H]
    calc
      2 * (D * s) + 1 ≤ 2 * (D * s) + s := by nlinarith only [hs]
      _ = (2 * D + 1) * s := by ring
  obtain ⟨Q, hQmem, hQcard⟩ :=
    exists_finset_signed_level_tube a H (fun _ : ℤ => (0 : ℝ)) I m hH.le
  have hQmem' (z : Lattice) :
      z ∈ Q ↔
        I ≤ z.1 + z.2 ∧ z.1 + z.2 ≤ I + (m : ℤ) ∧
          |(1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ)| ≤ H := by
    simpa only [sub_zero] using hQmem z
  have hQregion (z : Lattice) :
      z ∈ Q ↔
        |((z.1 + z.2 : ℤ) : ℝ)| ≤ M ∧
          |(1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ)| ≤ H := by
    rw [hQmem' z]
    constructor
    · rintro ⟨hlo, hrest⟩
      rcases hrest with ⟨hhi, htrans⟩
      exact ⟨(hlevel z).mp ⟨hlo, hhi⟩, htrans⟩
    · rintro ⟨hlevelBound, htrans⟩
      rcases (hlevel z).mpr hlevelBound with ⟨hlo, hhi⟩
      exact ⟨hlo, hhi, htrans⟩
  have hcardRegion : (Q.card : ℝ) ≤ (2 * M + 1) * (2 * H + 1) := by
    calc
      (Q.card : ℝ) ≤ ((m + 1 : ℕ) : ℝ) * (2 * H + 1) := hQcard
      _ ≤ (2 * M + 1) * (2 * H + 1) :=
        mul_le_mul_of_nonneg_right hcount (by positivity)
  have hCscale : 0 ≤ (2 * C + 1) * s^3 := by positivity
  have hHplus : 0 ≤ 2 * H + 1 := by positivity
  refine ⟨Q, ?_, ?_⟩
  · intro z
    simpa only [M, H, C, D] using hQregion z
  · calc
      (Q.card : ℝ) ≤ (2 * M + 1) * (2 * H + 1) := hcardRegion
      _ ≤ ((2 * C + 1) * s^3) * ((2 * D + 1) * s) :=
        mul_le_mul hlevelCount hHcount hHplus hCscale
      _ = (2 * C + 1) * (2 * D + 1) * s^4 := by ring
      _ = (2 * A + 11) * (2 * R + 4 * c₁ + 21) * s^4 := by
        dsimp only [C, D]
        ring

end LPPDifferentiability

end
