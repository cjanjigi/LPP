/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.LevelIntervalAttachments
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! Finite cardinal bounds for signed level strips and moving transverse centers. -/
public section

namespace LPPDifferentiability

/-- A finite set contains exactly the sites in signed levels with
level-dependent closed transverse windows. -/
theorem exists_finset_signed_level_window
    (a W : ℝ) (I : ℤ) (m : ℕ) (lo hi : ℤ → ℝ)
    (hW : 0 ≤ W)
    (hwindow : ∀ k, I ≤ k → k ≤ I + (m : ℤ) → lo k ≤ hi k)
    (hwidth : ∀ k, I ≤ k → k ≤ I + (m : ℤ) → hi k - lo k ≤ W) :
    ∃ Q : Finset Lattice,
      (∀ z, z ∈ Q ↔
        I ≤ z.1 + z.2 ∧ z.1 + z.2 ≤ I + (m : ℤ) ∧
          lo (z.1 + z.2) ≤ (1-a)*(z.1:ℝ)-a*(z.2:ℝ) ∧
          (1-a)*(z.1:ℝ)-a*(z.2:ℝ) ≤ hi (z.1 + z.2)) ∧
      (Q.card : ℝ) ≤ ((m + 1 : ℕ) : ℝ) * (W + 1) := by
  classical
  let levels : Finset ℤ := Finset.Icc I (I + (m : ℤ))
  let slice : ℤ → Finset Lattice := fun k =>
    if hk : k ∈ levels then
      Classical.choose (exists_finset_level_interval a (lo k) (hi k) k
        (hwindow k (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2))
    else ∅
  have hslice (k : ℤ) (hk : k ∈ levels) :
      (∀ z, z ∈ slice k ↔
        z.1 + z.2 = k ∧ lo k ≤ (1-a)*(z.1:ℝ)-a*(z.2:ℝ) ∧
          (1-a)*(z.1:ℝ)-a*(z.2:ℝ) ≤ hi k) ∧
      ((slice k).card : ℝ) ≤ hi k - lo k + 1 := by
    have hchosen := Classical.choose_spec
      (exists_finset_level_interval a (lo k) (hi k) k
        (hwindow k (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2))
    dsimp only [slice]
    rw [dite_eq_left hk]
    exact ⟨by simpa only [Set.mem_Icc] using hchosen.1, hchosen.2⟩
  let Q : Finset Lattice := levels.biUnion slice
  have hQmem (z : Lattice) :
      z ∈ Q ↔
        I ≤ z.1 + z.2 ∧ z.1 + z.2 ≤ I + (m : ℤ) ∧
          lo (z.1 + z.2) ≤ (1-a)*(z.1:ℝ)-a*(z.2:ℝ) ∧
          (1-a)*(z.1:ℝ)-a*(z.2:ℝ) ≤ hi (z.1 + z.2) := by
    dsimp only [Q]
    constructor
    · intro hz
      rcases Finset.mem_biUnion.mp hz with ⟨k, hk, hzk⟩
      rcases Finset.mem_Icc.mp hk with ⟨hklo, hkhi⟩
      rcases ((hslice k (Finset.mem_Icc.mpr ⟨hklo, hkhi⟩)).1 z).mp hzk with
        ⟨hlevel, htranslo, htranshi⟩
      rw [← hlevel] at hklo hkhi htranslo htranshi
      exact ⟨hklo, hkhi, htranslo, htranshi⟩
    · rintro ⟨hzlo, hzhi, htranslo, htranshi⟩
      have hk : z.1 + z.2 ∈ levels := Finset.mem_Icc.mpr ⟨hzlo, hzhi⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨z.1 + z.2, hk, ?_⟩
      exact ((hslice (z.1 + z.2) hk).1 z).mpr
        ⟨rfl, htranslo, htranshi⟩
  have hbi : Q.card ≤ ∑ k ∈ levels, (slice k).card := by
    dsimp only [Q, levels]
    exact Finset.card_biUnion_le
  have hbiR : (Q.card : ℝ) ≤ ∑ k ∈ levels, ((slice k).card : ℝ) := by
    calc
      (Q.card : ℝ) ≤ ((∑ k ∈ levels, (slice k).card : ℕ) : ℝ) := by
        exact_mod_cast hbi
      _ = ∑ k ∈ levels, ((slice k).card : ℝ) := by norm_cast
  have hsum :
      (∑ k ∈ levels, ((slice k).card : ℝ)) ≤ ∑ k ∈ levels, (W + 1) := by
    apply Finset.sum_le_sum
    intro k hk
    rcases Finset.mem_Icc.mp hk with ⟨hklo, hkhi⟩
    calc
      ((slice k).card : ℝ) ≤ hi k - lo k + 1 := (hslice k hk).2
      _ ≤ W + 1 := by linarith only [hwidth k hklo hkhi]
  have hlevelsZ : (levels.card : ℤ) = (m + 1 : ℤ) := by
    dsimp only [levels]
    rw [Int.card_Icc_of_le (a := I) (b := I + (m : ℤ)) (by omega)]
    omega
  have hlevelsR : (levels.card : ℝ) = ((m + 1 : ℕ) : ℝ) := by
    exact_mod_cast hlevelsZ
  have hconst : (∑ k ∈ levels, (W + 1)) =
      (levels.card : ℝ) * (W + 1) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hlevelsLe : (levels.card : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
    rw [hlevelsR]
  refine ⟨Q, hQmem, ?_⟩
  calc
    (Q.card : ℝ) ≤ ∑ k ∈ levels, ((slice k).card : ℝ) := hbiR
    _ ≤ ∑ k ∈ levels, (W + 1) := hsum
    _ = (levels.card : ℝ) * (W + 1) := hconst
    _ ≤ ((m + 1 : ℕ) : ℝ) * (W + 1) :=
      mul_le_mul_of_nonneg_right hlevelsLe (by linarith [hW])

/-- A moving-center tube has at most `2h+1` lattice sites per signed level. -/
theorem exists_finset_signed_level_tube
    (a h : ℝ) (r : ℤ → ℝ) (I : ℤ) (m : ℕ) (hh : 0 ≤ h) :
    ∃ Q : Finset Lattice,
      (∀ z, z ∈ Q ↔
        I ≤ z.1 + z.2 ∧ z.1 + z.2 ≤ I + (m : ℤ) ∧
          |(1-a)*(z.1:ℝ)-a*(z.2:ℝ)-r (z.1 + z.2)| ≤ h) ∧
      (Q.card : ℝ) ≤ ((m + 1 : ℕ) : ℝ) * (2*h+1) := by
  obtain ⟨Q, hQmem, hQcard⟩ :=
    exists_finset_signed_level_window a (2*h) I m
      (fun k => r k - h) (fun k => r k + h)
      (mul_nonneg (by norm_num) hh)
      (by intro k _ _; linarith)
      (by intro k _ _; nlinarith)
  refine ⟨Q, ?_, hQcard⟩
  intro z
  rw [hQmem z]
  constructor
  · rintro ⟨hzlo, hzhi, htranslo, htranshi⟩
    refine ⟨hzlo, hzhi, abs_le.mpr ⟨?_, ?_⟩⟩ <;> linarith
  · rintro ⟨hzlo, hzhi, htrans⟩
    rcases abs_le.mp htrans with ⟨htranslo, htranshi⟩
    exact ⟨hzlo, hzhi, by linarith, by linarith⟩

/-- The half-width `K+2` gives the exact per-level count `2K+5`. -/
theorem exists_finset_signed_level_nat_tube
    (a : ℝ) (r : ℤ → ℝ) (I : ℤ) (m K : ℕ) :
    ∃ Q : Finset Lattice,
      (∀ z, z ∈ Q ↔
        I ≤ z.1 + z.2 ∧ z.1 + z.2 ≤ I + (m : ℤ) ∧
          |(1-a)*(z.1:ℝ)-a*(z.2:ℝ)-r (z.1 + z.2)| ≤ (K : ℝ) + 2) ∧
      (Q.card : ℝ) ≤ ((m + 1 : ℕ) : ℝ) * (2*(K : ℝ)+5) := by
  obtain ⟨Q, hQmem, hQcard⟩ :=
    exists_finset_signed_level_tube a ((K : ℝ)+2) r I m (by positivity)
  have hconstant : 2*((K : ℝ)+2)+1 = 2*(K : ℝ)+5 := by ring
  refine ⟨Q, hQmem, ?_⟩
  calc
    (Q.card : ℝ) ≤ ((m + 1 : ℕ) : ℝ) * (2*((K : ℝ)+2)+1) := hQcard
    _ = ((m + 1 : ℕ) : ℝ) * (2*(K : ℝ)+5) := by rw [hconstant]

end LPPDifferentiability

end
