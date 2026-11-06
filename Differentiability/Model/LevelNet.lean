/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.Lattice
public import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-! Integer grids used to construct finite nets on arbitrary signed levels. -/

public section

namespace LPPDifferentiability

/-- The floor/ceiling construction, retaining its strict source counting bound.
The scalar offset `c` is later instantiated by `a * I`. -/
theorem exists_integer_level_grid (t A B c : ℝ) (ht : 1 ≤ t)
    (hwidth : 8 * t ≤ B - A) :
    ∃ (M : ℕ) (p q : ℤ),
      1 ≤ M ∧ t ≤ (q : ℝ) ∧ (q : ℝ) ≤ 2 * t ∧
      A ≤ (p : ℝ) - c ∧ (p : ℝ) - c ≤ A + 2 * t ∧
      A + 2 * t < (p : ℝ) + (q : ℝ) - c ∧
      B - 2 * t ≤ (p : ℝ) + M * (q : ℝ) - c ∧
      (p : ℝ) + M * (q : ℝ) - c ≤ B ∧
      (∀ j : ℕ, j < M → (p : ℝ) + j * (q : ℝ) - c < B - 2 * t) ∧
      (M + 1 : ℝ) < (B - A) / t := by
  let p : ℤ := ⌊A + 2 * t + c⌋
  let q : ℤ := ⌈t⌉
  let x : ℝ := (p : ℝ) - c
  have htpos : 0 < t := by linarith
  have hq : t ≤ (q : ℝ) := Int.le_ceil t
  have hqlt : (q : ℝ) < t + 1 := Int.ceil_lt_add_one t
  have hqpos : 0 < (q : ℝ) := lt_of_lt_of_le htpos hq
  have hqhi : (q : ℝ) ≤ 2 * t := by linarith
  have hxhi : x ≤ A + 2 * t := by
    have := Int.floor_le (A + 2 * t + c)
    dsimp [x, p]
    linarith
  have hxlo : A + 2 * t - 1 < x := by
    have := Int.lt_floor_add_one (A + 2 * t + c)
    dsimp [x, p]
    linarith
  have hxA : A ≤ x := by linarith
  have hxnext : A + 2 * t < x + (q : ℝ) := by linarith
  let d : ℝ := (B - 2 * t - x) / (q : ℝ)
  have hdpos : 0 < d := by
    dsimp [d]
    exact div_pos (by linarith) hqpos
  let M : ℕ := ⌈d⌉₊
  have hMpos : 1 ≤ M := Nat.ceil_pos.mpr hdpos
  have hdM : d ≤ (M : ℝ) := Nat.le_ceil d
  have hMd : (M : ℝ) < d + 1 := Nat.ceil_lt_add_one hdpos.le
  have hdq : d * (q : ℝ) = B - 2 * t - x := by
    dsimp [d]
    exact div_mul_cancel₀ _ hqpos.ne'
  have hlastlo : B - 2 * t ≤ x + M * (q : ℝ) := by
    have := mul_le_mul_of_nonneg_right hdM hqpos.le
    linarith
  have hlastlt : x + M * (q : ℝ) < B - 2 * t + (q : ℝ) := by
    have := mul_lt_mul_of_pos_right hMd hqpos
    nlinarith only [this, hdq]
  have hlastB : x + M * (q : ℝ) ≤ B := by linarith
  have hbefore : ∀ j : ℕ, j < M → x + j * (q : ℝ) < B - 2 * t := by
    intro j hj
    have hjM : (j : ℝ) + 1 ≤ M := by exact_mod_cast hj
    have hjd : (j : ℝ) < d := by linarith
    have := mul_lt_mul_of_pos_right hjd hqpos
    linarith
  have hcount : (M + 1 : ℝ) < (B - A) / t := by
    apply (lt_div_iff₀ htpos).mpr
    by_cases hM : 2 ≤ M
    · have hMr : (2 : ℝ) ≤ M := by exact_mod_cast hM
      have hpen : x + ((M : ℝ) - 1) * (q : ℝ) < B - 2 * t := by
        have := mul_lt_mul_of_pos_right hMd hqpos
        nlinarith only [this, hdq]
      have hspan : ((M : ℝ) - 2) * (q : ℝ) < B - A - 4 * t := by
        nlinarith only [hpen, hxnext]
      have hscale := mul_le_mul_of_nonneg_left hq (sub_nonneg.mpr hMr)
      nlinarith only [hscale, hspan, htpos]
    · have hMeq : M = 1 := by omega
      rw [hMeq]
      norm_num
      linarith
  refine ⟨M, p, q, hMpos, hq, hqhi, hxA, hxhi, ?_, ?_, ?_, ?_, hcount⟩
  · dsimp [x] at hxnext
    linarith only [hxnext]
  · dsimp [x] at hlastlo
    linarith only [hlastlo]
  · dsimp [x] at hlastB
    linarith only [hlastB]
  · intro j hj
    have h := hbefore j hj
    dsimp [x] at h
    linarith only [h]

/-- A closed interval within a finite increasing grid's span, of length at
least the maximal gap, contains a grid point. -/
theorem finite_grid_interval_coverage (M : ℕ) (x : Fin (M + 1) → ℝ)
    (L U g : ℝ) (hg : 0 ≤ g) (hLU : L + g ≤ U)
    (hfirst : x ⟨0, by omega⟩ ≤ L) (hlast : U ≤ x ⟨M, by omega⟩)
    (hgap : ∀ j : ℕ, (hj : j < M) →
      x ⟨j + 1, by omega⟩ - x ⟨j, by omega⟩ ≤ g) :
    ∃ j, L ≤ x j ∧ x j ≤ U := by
  classical
  by_cases hzero : L ≤ x ⟨0, by omega⟩
  · exact ⟨⟨0, by omega⟩, hzero, (hfirst.trans (by linarith))⟩
  have hex : ∃ j : ℕ, ∃ hj : j ≤ M, L ≤ x ⟨j, by omega⟩ :=
    ⟨M, le_rfl, by linarith⟩
  let j := Nat.find hex
  have hj := Nat.find_spec hex
  obtain ⟨hjM, hjL⟩ := hj
  have hjpos : 0 < j := by
    by_contra hn
    have hjzero : j = 0 := by omega
    have hjfind : Nat.find hex = 0 := hjzero
    have hfin : (⟨Nat.find hex, by omega⟩ : Fin (M+1)) = ⟨0, by omega⟩ :=
      Fin.ext hjfind
    rw [hfin] at hjL
    exact hzero hjL
  have hprev : x ⟨j - 1, by omega⟩ < L := by
    have h := Nat.find_min hex (show j - 1 < j by omega)
    apply lt_of_not_ge
    intro hh
    exact h ⟨by omega, hh⟩
  refine ⟨⟨j, by omega⟩, hjL, ?_⟩
  have hg := hgap (j - 1) (by omega)
  have heq : j - 1 + 1 = j := by omega
  simp only [heq] at hg
  linarith

end LPPDifferentiability
