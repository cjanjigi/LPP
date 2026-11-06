/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.Quadrant

import Mathlib.Tactic
import Martin2004.Analysis.DyadicQuadrantGrid
import Martin2004.Analysis.FiniteQuadrantGrid

/-!
# Dyadic grid error with a requested lower cutoff

The compact modulus gives one mesh cutoff that works at every dyadic scale.
This version also makes that cutoff at least any prescribed natural number.
-/

public section

open scoped Topology NNReal

namespace LPPDifferentiability

/-- Given any requested lower bound, choose one dyadic mesh cutoff at least that
large and at least four which controls every lower-grid approximation in every
shell for the same continuous, homogeneous function. The function may have
either sign. -/
theorem exists_uniform_dyadic_quadrant_grid_shape_error_of_lower_bound
    (g : Quadrant → ℝ) (hg : Continuous g)
    (hhom : ∀ (c : ℝ≥0) (x : Quadrant), g (c • x) = (c : ℝ) * g x)
    (ε : ℝ) (hε : 0 < ε) (Q : ℕ) :
    ∃ q : ℕ, 4 ≤ q ∧ Q ≤ q ∧ ∀ k : ℕ, ∀ z : ℕ × ℕ,
      q * 2 ^ k ≤ z.1 + z.2 → z.1 + z.2 < 2 * (q * 2 ^ k) →
      |g ((z.1 : ℝ≥0), (z.2 : ℝ≥0)) -
        g (((2 ^ k * (z.1 / 2 ^ k) : ℕ) : ℝ≥0),
          ((2 ^ k * (z.2 / 2 ^ k) : ℕ) : ℝ≥0))| ≤
        ε * ((z.1 + z.2 : ℕ) : ℝ) := by
  let a : ℝ := ε / 2
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨δ, hδ, hmod⟩ := continuous_quadrant_unit_square_modulus g hg ha
  obtain ⟨q₀, hq₀⟩ := exists_nat_one_div_lt hδ
  let q : ℕ := max Q (q₀ + 5)
  have hq : 4 ≤ q := by dsimp [q]; omega
  have hqQ : Q ≤ q := le_max_left Q (q₀ + 5)
  have hqextra : q₀ + 5 ≤ q := le_max_right Q (q₀ + 5)
  have hqpos : 0 < q := lt_of_lt_of_le (by decide) hq
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hqpos
  have hq₀R : 0 < ((q₀ + 1 : ℕ) : ℝ) := by positivity
  have hq₀lt : q₀ + 1 < q := by omega
  have hqrecip : (1 : ℝ) / (q : ℝ) < 1 / ((q₀ + 1 : ℕ) : ℝ) :=
    one_div_lt_one_div_of_lt hq₀R (by exact_mod_cast hq₀lt)
  have hq₀' : (1 : ℝ) / ((q₀ + 1 : ℕ) : ℝ) < δ := by
    simpa only [Nat.cast_add, Nat.cast_one] using hq₀
  have hqmesh : (1 : ℝ) / (q : ℝ) < δ := hqrecip.trans hq₀'
  have hhalfmesh : (1 : ℝ) / (2 * (q : ℝ)) < δ := by
    exact (one_div_lt_one_div_of_lt hqR (by nlinarith only [hqR])).trans hqmesh
  refine ⟨q, hq, hqQ, ?_⟩
  intro k z hzlo hzhi
  let h : ℕ := 2 ^ k
  have hh : 0 < h := Nat.pow_pos (by decide)
  let m : ℕ := q * h
  have hm : 0 < m := Nat.mul_pos hqpos hh
  let n : ℝ≥0 := ((2 * m : ℕ) : ℝ≥0)
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast Nat.mul_pos (by decide) hm
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnR_eq : (n : ℝ) = 2 * ((m : ℕ) : ℝ) := by
    simp [n, NNReal.coe_natCast, Nat.cast_mul]
  have hscale_den : (1 : ℝ) / (2 * (q : ℝ)) * (n : ℝ) = (h : ℝ) := by
    rw [hnR_eq]
    dsimp [m]
    push_cast
    field_simp [hqR.ne']
  let w : ℕ × ℕ := (h * (z.1 / h), h * (z.2 / h))
  have hgeom := dyadic_quadrant_grid_rounding_properties q h hq hh z
    (by simpa [h] using hzlo) (by simpa [h, m] using hzhi)
  change
    w.1 ≤ z.1 ∧ w.2 ≤ z.2 ∧ z.1 - w.1 < h ∧ z.2 - w.2 < h ∧
      (z.1 - w.1) + (z.2 - w.2) < 2 * h ∧
      ∃ i j : ℕ, i ≤ 2 * q ∧ j ≤ 2 * q ∧
        w = (h * i, h * j) ∧ w + (z - w) = z ∧ z ≠ (0, 0) at hgeom
  rcases hgeom with ⟨hw₁, hw₂, hgap₁, hgap₂, _, _⟩
  have hz₁ : z.1 < 2 * m := by
    apply lt_of_le_of_lt (Nat.le_add_right z.1 z.2)
    simpa [h, m] using hzhi
  have hz₂ : z.2 < 2 * m := by
    apply lt_of_le_of_lt (Nat.le_add_left z.2 z.1)
    simpa [h, m, Nat.add_comm] using hzhi
  let x : Quadrant := ((z.1 : ℝ≥0) / n, (z.2 : ℝ≥0) / n)
  let y : Quadrant := ((w.1 : ℝ≥0) / n, (w.2 : ℝ≥0) / n)
  have hx₁ : x.1 ≤ 1 := by
    change (z.1 : ℝ≥0) / n ≤ 1
    apply (div_le_one₀ hn).2
    change (z.1 : ℝ≥0) ≤ ((2 * m : ℕ) : ℝ≥0)
    exact_mod_cast Nat.le_of_lt hz₁
  have hx₂ : x.2 ≤ 1 := by
    change (z.2 : ℝ≥0) / n ≤ 1
    apply (div_le_one₀ hn).2
    change (z.2 : ℝ≥0) ≤ ((2 * m : ℕ) : ℝ≥0)
    exact_mod_cast Nat.le_of_lt hz₂
  have hy₁ : y.1 ≤ 1 := by
    change (w.1 : ℝ≥0) / n ≤ 1
    apply (div_le_one₀ hn).2
    change (w.1 : ℝ≥0) ≤ ((2 * m : ℕ) : ℝ≥0)
    exact_mod_cast (Nat.le_trans hw₁ (Nat.le_of_lt hz₁))
  have hy₂ : y.2 ≤ 1 := by
    change (w.2 : ℝ≥0) / n ≤ 1
    apply (div_le_one₀ hn).2
    change (w.2 : ℝ≥0) ≤ ((2 * m : ℕ) : ℝ≥0)
    exact_mod_cast (Nat.le_trans hw₂ (Nat.le_of_lt hz₂))
  have hyx₁ : y.1 ≤ x.1 := by
    change (w.1 : ℝ≥0) / n ≤ (z.1 : ℝ≥0) / n
    exact (div_le_div_iff_of_pos_right hn).2 (by exact_mod_cast hw₁)
  have hyx₂ : y.2 ≤ x.2 := by
    change (w.2 : ℝ≥0) / n ≤ (z.2 : ℝ≥0) / n
    exact (div_le_div_iff_of_pos_right hn).2 (by exact_mod_cast hw₂)
  have hgap₁R : (z.1 : ℝ) - (w.1 : ℝ) < (h : ℝ) := by
    exact_mod_cast hgap₁
  have hgap₂R : (z.2 : ℝ) - (w.2 : ℝ) < (h : ℝ) := by
    exact_mod_cast hgap₂
  have hnormgap₁ : (z.1 : ℝ) / (n : ℝ) - (w.1 : ℝ) / (n : ℝ) <
      (1 : ℝ) / (2 * (q : ℝ)) := by
    rw [← sub_div]
    apply (div_lt_iff₀ hnR).2
    rw [hscale_den]
    exact hgap₁R
  have hnormgap₂ : (z.2 : ℝ) / (n : ℝ) - (w.2 : ℝ) / (n : ℝ) <
      (1 : ℝ) / (2 * (q : ℝ)) := by
    rw [← sub_div]
    apply (div_lt_iff₀ hnR).2
    rw [hscale_den]
    exact hgap₂R
  have hdist : dist x y < δ := by
    rw [Prod.dist_eq, max_lt_iff]
    constructor
    · rw [NNReal.dist_eq]
      rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hyx₁))]
      dsimp only [x, y]
      simp only [NNReal.coe_div]
      exact hnormgap₁.trans hhalfmesh
    · rw [NNReal.dist_eq]
      rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hyx₂))]
      dsimp only [x, y]
      simp only [NNReal.coe_div]
      exact hnormgap₂.trans hhalfmesh
  have hx : x ≤ (1, 1) := ⟨hx₁, hx₂⟩
  have hy : y ≤ (1, 1) := ⟨hy₁, hy₂⟩
  have hshape : |g x - g y| < a := hmod x y hx hy hdist
  let zq : Quadrant := ((z.1 : ℝ≥0), (z.2 : ℝ≥0))
  let wq : Quadrant := ((w.1 : ℝ≥0), (w.2 : ℝ≥0))
  have hscaleX : n • x = zq := by
    apply Prod.ext
    · change n * ((z.1 : ℝ≥0) / n) = (z.1 : ℝ≥0)
      exact mul_div_cancel₀ _ hn.ne'
    · change n * ((z.2 : ℝ≥0) / n) = (z.2 : ℝ≥0)
      exact mul_div_cancel₀ _ hn.ne'
  have hscaleY : n • y = wq := by
    apply Prod.ext
    · change n * ((w.1 : ℝ≥0) / n) = (w.1 : ℝ≥0)
      exact mul_div_cancel₀ _ hn.ne'
    · change n * ((w.2 : ℝ≥0) / n) = (w.2 : ℝ≥0)
      exact mul_div_cancel₀ _ hn.ne'
  have hgx : g zq = (n : ℝ) * g x := by
    rw [← hscaleX, hhom]
  have hgy : g wq = (n : ℝ) * g y := by
    rw [← hscaleY, hhom]
  have hshapeR : |g zq - g wq| < ε * ((m : ℕ) : ℝ) := by
    have hmul := mul_lt_mul_of_pos_left hshape hnR
    calc
      |g zq - g wq| = (n : ℝ) * |g x - g y| := by
        rw [hgx, hgy, ← mul_sub, abs_mul, abs_of_nonneg hnR.le]
      _ < (n : ℝ) * (ε / 2) := by simpa [a] using hmul
      _ = ε * ((m : ℕ) : ℝ) := by rw [hnR_eq]; ring
  have hlen : m ≤ z.1 + z.2 := by simpa [m, h] using hzlo
  have hlenR : ((m : ℕ) : ℝ) ≤ ((z.1 + z.2 : ℕ) : ℝ) := by exact_mod_cast hlen
  have hfinal : |g zq - g wq| < ε * ((z.1 + z.2 : ℕ) : ℝ) :=
    hshapeR.trans_le (mul_le_mul_of_nonneg_left hlenR hε.le)
  exact le_of_lt hfinal

end LPPDifferentiability

end
