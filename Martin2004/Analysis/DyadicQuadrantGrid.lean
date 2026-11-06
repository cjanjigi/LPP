/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.Quadrant

import Mathlib.Data.Nat.BinaryRec
import Mathlib.Tactic
import Martin2004.Analysis.FiniteQuadrantGrid

/-!
# Dyadic grids in the closed quadrant

Coordinatewise division by a positive mesh rounds a natural endpoint down to a
finite list of directions. Dyadic length shells cover all sufficiently large
natural lengths. Compact continuity then controls the change in one continuous,
homogeneous function between an endpoint and its rounded point.
-/

public section

open scoped Topology NNReal

namespace LPPDifferentiability

/-- Rounding a shell endpoint down by a positive mesh gives a lower grid
point, coordinate errors below one mesh width, and a direction in the finite
square `0 ≤ i,j ≤ 2q`. The endpoint decomposition uses coordinatewise natural
subtraction. -/
theorem dyadic_quadrant_grid_rounding_properties
    (q h : ℕ) (hq : 4 ≤ q) (hh : 0 < h) (z : ℕ × ℕ)
    (hzlo : q * h ≤ z.1 + z.2)
    (hzhi : z.1 + z.2 < 2 * (q * h)) :
    let w : ℕ × ℕ := (h * (z.1 / h), h * (z.2 / h))
    w.1 ≤ z.1 ∧ w.2 ≤ z.2 ∧
      z.1 - w.1 < h ∧ z.2 - w.2 < h ∧
      (z.1 - w.1) + (z.2 - w.2) < 2 * h ∧
      ∃ i j : ℕ, i ≤ 2 * q ∧ j ≤ 2 * q ∧
        w = (h * i, h * j) ∧ w + (z - w) = z ∧ z ≠ (0, 0) := by
  let w : ℕ × ℕ := (h * (z.1 / h), h * (z.2 / h))
  change
    w.1 ≤ z.1 ∧ w.2 ≤ z.2 ∧
      z.1 - w.1 < h ∧ z.2 - w.2 < h ∧
      (z.1 - w.1) + (z.2 - w.2) < 2 * h ∧
      ∃ i j : ℕ, i ≤ 2 * q ∧ j ≤ 2 * q ∧
        w = (h * i, h * j) ∧ w + (z - w) = z ∧ z ≠ (0, 0)
  have hw₁ : w.1 ≤ z.1 := by
    dsimp [w]
    exact Nat.mul_div_le _ _
  have hw₂ : w.2 ≤ z.2 := by
    dsimp [w]
    exact Nat.mul_div_le _ _
  have hdivision₁ : h * (z.1 / h) + z.1 % h = z.1 := Nat.div_add_mod z.1 h
  have hdivision₂ : h * (z.2 / h) + z.2 % h = z.2 := Nat.div_add_mod z.2 h
  have hgap₁ : z.1 - w.1 < h := by
    have hrem := Nat.mod_lt z.1 hh
    dsimp [w]
    omega
  have hgap₂ : z.2 - w.2 < h := by
    have hrem := Nat.mod_lt z.2 hh
    dsimp [w]
    omega
  have hdisplacement : (z.1 - w.1) + (z.2 - w.2) < 2 * h := by
    omega
  have horigin : z ≠ (0, 0) := by
    have hqpos : 0 < q := lt_of_lt_of_le (by decide) hq
    have hprod : 0 < q * h := Nat.mul_pos hqpos hh
    rintro rfl
    simp at hzlo
    omega
  have hz₁ : z.1 < (2 * q) * h := by
    have hupper : z.1 + z.2 < (2 * q) * h := by
      calc
        z.1 + z.2 < 2 * (q * h) := hzhi
        _ = (2 * q) * h := by ring
    exact lt_of_le_of_lt (Nat.le_add_right z.1 z.2) hupper
  have hz₂ : z.2 < (2 * q) * h := by
    have hupper : z.1 + z.2 < (2 * q) * h := by
      calc
        z.1 + z.2 < 2 * (q * h) := hzhi
        _ = (2 * q) * h := by ring
    exact lt_of_le_of_lt (Nat.le_add_left z.2 z.1) (by simpa [Nat.add_comm] using hupper)
  have hdirection₁ : z.1 / h < 2 * q :=
    (Nat.div_lt_iff_lt_mul hh).2 hz₁
  have hdirection₂ : z.2 / h < 2 * q :=
    (Nat.div_lt_iff_lt_mul hh).2 hz₂
  refine ⟨hw₁, hw₂, hgap₁, hgap₂, hdisplacement, ?_⟩
  refine ⟨z.1 / h, z.2 / h, Nat.le_of_lt hdirection₁,
    Nat.le_of_lt hdirection₂, ?_, ?_, horigin⟩
  · rfl
  · apply Prod.ext
    · dsimp
      omega
    · dsimp
      omega

/-- Every natural length at least `q` lies in one of the dyadic shells
`[q * 2^k, q * 2^(k+1))`. -/
theorem exists_dyadic_quadrant_length_shell
    (q n : ℕ) (hq : 0 < q) (hn : q ≤ n) :
    ∃ k : ℕ, q * 2 ^ k ≤ n ∧ n < q * 2 ^ (k + 1) := by
  let k : ℕ := Nat.log2 (n / q)
  have hnq : 0 < n / q := Nat.div_pos hn hq
  have hnq_ne : n / q ≠ 0 := Nat.ne_of_gt hnq
  have hpowlo : 2 ^ Nat.log2 (n / q) ≤ n / q := Nat.log2_self_le hnq_ne
  have hpowhi : n / q < 2 ^ (Nat.log2 (n / q) + 1) := Nat.lt_log2_self
  have hlo : q * 2 ^ k ≤ n := by
    dsimp [k]
    calc
      q * 2 ^ Nat.log2 (n / q) = 2 ^ Nat.log2 (n / q) * q := Nat.mul_comm _ _
      _ ≤ n := Nat.mul_le_of_le_div _ _ _ hpowlo
  have hhi : n < q * 2 ^ (k + 1) := by
    have hquot : n / q < 2 ^ (k + 1) := by simpa [k] using hpowhi
    have hmul : n < 2 ^ (k + 1) * q := (Nat.div_lt_iff_lt_mul hq).mp hquot
    calc
      n < 2 ^ (k + 1) * q := hmul
      _ = q * 2 ^ (k + 1) := Nat.mul_comm _ _
  exact ⟨k, hlo, hhi⟩

/-- Once a length reaches `q * 2^K`, every shell index covering it is at
least `K`. -/
theorem dyadic_quadrant_shell_index_eventually_large
    (q K n : ℕ) (hq : 0 < q) (hn : q * 2 ^ K ≤ n) :
    ∃ k : ℕ, K ≤ k ∧ q * 2 ^ k ≤ n ∧ n < q * 2 ^ (k + 1) := by
  have hpowpos : 0 < 2 ^ K := Nat.pow_pos (by decide)
  have hpowone : 1 ≤ 2 ^ K := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hpowpos)
  have hqle : q ≤ n := by
    apply le_trans (b := q * 2 ^ K)
    · calc
        q = q * 1 := by simp
        _ ≤ q * 2 ^ K := Nat.mul_le_mul_left q hpowone
    · exact hn
  obtain ⟨k, hlo, hhi⟩ := exists_dyadic_quadrant_length_shell q n hq hqle
  have hK : K ≤ k := by
    by_contra hnot
    have hk : k < K := Nat.lt_of_not_ge hnot
    have hsucc : k + 1 ≤ K := Nat.succ_le_of_lt hk
    have hpow : 2 ^ (k + 1) ≤ 2 ^ K := Nat.pow_le_pow_right (by decide) hsucc
    have hupper : n < q * 2 ^ K := lt_of_lt_of_le hhi (Nat.mul_le_mul_left q hpow)
    omega
  exact ⟨k, hK, hlo, hhi⟩

/-- A positive-mesh shell cannot contain the origin. The shell convention
therefore needs no division by the endpoint length. -/
theorem dyadic_quadrant_shell_endpoint_ne_origin
    (q h : ℕ) (hq : 4 ≤ q) (hh : 0 < h) (z : ℕ × ℕ)
    (hzlo : q * h ≤ z.1 + z.2) : z ≠ (0, 0) := by
  have hqpos : 0 < q := lt_of_lt_of_le (by decide) hq
  have hprod : 0 < q * h := Nat.mul_pos hqpos hh
  rintro rfl
  simp at hzlo
  omega

/-- One modulus for the same continuous, positively homogeneous quadrant
function controls every lower-grid approximation in every shell. No sign or
positivity assumption on the function is required. -/
theorem exists_uniform_dyadic_quadrant_grid_shape_error
    (g : Quadrant → ℝ) (hg : Continuous g)
    (hhom : ∀ (c : ℝ≥0) (x : Quadrant), g (c • x) = (c : ℝ) * g x)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ q : ℕ, 4 ≤ q ∧ ∀ k : ℕ, ∀ z : ℕ × ℕ,
      q * 2 ^ k ≤ z.1 + z.2 → z.1 + z.2 < 2 * (q * 2 ^ k) →
      |g ((z.1 : ℝ≥0), (z.2 : ℝ≥0)) -
        g (((2 ^ k * (z.1 / 2 ^ k) : ℕ) : ℝ≥0),
          ((2 ^ k * (z.2 / 2 ^ k) : ℕ) : ℝ≥0))| ≤
        ε * ((z.1 + z.2 : ℕ) : ℝ) := by
  let a : ℝ := ε / 2
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨δ, hδ, hmod⟩ := continuous_quadrant_unit_square_modulus g hg ha
  obtain ⟨q₀, hq₀⟩ := exists_nat_one_div_lt hδ
  let q : ℕ := q₀ + 5
  have hq : 4 ≤ q := by dsimp [q]; omega
  have hqpos : 0 < q := lt_of_lt_of_le (by decide) hq
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hqpos
  have hq₀R : 0 < ((q₀ + 1 : ℕ) : ℝ) := by positivity
  have hq₀lt : q₀ + 1 < q := by dsimp [q]; omega
  have hqrecip : (1 : ℝ) / (q : ℝ) < 1 / ((q₀ + 1 : ℕ) : ℝ) :=
    one_div_lt_one_div_of_lt hq₀R (by exact_mod_cast hq₀lt)
  have hq₀' : (1 : ℝ) / ((q₀ + 1 : ℕ) : ℝ) < δ := by
    simpa only [Nat.cast_add, Nat.cast_one] using hq₀
  have hqmesh : (1 : ℝ) / (q : ℝ) < δ := hqrecip.trans hq₀'
  have hhalfmesh : (1 : ℝ) / (2 * (q : ℝ)) < δ := by
    exact (one_div_lt_one_div_of_lt hqR (by nlinarith only [hqR])).trans hqmesh
  refine ⟨q, hq, ?_⟩
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

example :
    (let w : ℕ × ℕ := (1 * (0 / 1), 1 * (4 / 1))
     w.1 ≤ 0 ∧ w.2 ≤ 4 ∧ 0 - w.1 < 1 ∧ 4 - w.2 < 1 ∧
       (0 - w.1) + (4 - w.2) < 2 ∧
       ∃ i j : ℕ, i ≤ 8 ∧ j ≤ 8 ∧ w = (1 * i, 1 * j) ∧
         w + ((0, 4) - w) = (0, 4) ∧ (0, 4) ≠ (0, 0)) := by
  exact dyadic_quadrant_grid_rounding_properties 4 1 (by norm_num) (by norm_num)
    (0, 4) (by norm_num) (by norm_num)

example :
    (let w : ℕ × ℕ := (2 * (0 / 2), 2 * (9 / 2))
     w = (0, 8) ∧ 0 - w.1 = 0 ∧ 9 - w.2 = 1 ∧
       0 - w.1 < 2 ∧ 9 - w.2 < 2 ∧
       (0 - w.1) + (9 - w.2) < 4) := by
  have hgeom := dyadic_quadrant_grid_rounding_properties 4 2 (by norm_num) (by norm_num)
    (0, 9) (by norm_num) (by norm_num)
  change
    (let w : ℕ × ℕ := (2 * (0 / 2), 2 * (9 / 2))
     w.1 ≤ 0 ∧ w.2 ≤ 9 ∧ 0 - w.1 < 2 ∧ 9 - w.2 < 2 ∧
       (0 - w.1) + (9 - w.2) < 4 ∧
       ∃ i j : ℕ, i ≤ 8 ∧ j ≤ 8 ∧ w = (2 * i, 2 * j) ∧
         w + ((0, 9) - w) = (0, 9) ∧ (0, 9) ≠ (0, 0)) at hgeom
  rcases hgeom with ⟨hw₁, hw₂, hgap₁, hgap₂, hdisp, _⟩
  refine ⟨?_, ?_, ?_, hgap₁, hgap₂, hdisp⟩
  · norm_num
  · norm_num at hw₁ ⊢
  · norm_num at hgap₂ ⊢

example (ε : ℝ) (hε : 0 < ε) :
    ∃ q : ℕ, 4 ≤ q ∧ ∀ k : ℕ, ∀ z : ℕ × ℕ,
      q * 2 ^ k ≤ z.1 + z.2 → z.1 + z.2 < 2 * (q * 2 ^ k) →
      |(0 : ℝ) - (0 : ℝ)| ≤ ε * ((z.1 + z.2 : ℕ) : ℝ) := by
  have hzero : Continuous (fun _ : Quadrant => (0 : ℝ)) := continuous_const
  have hzero_hom : ∀ (c : ℝ≥0) (x : Quadrant),
      (fun _ : Quadrant => (0 : ℝ)) (c • x) = (c : ℝ) *
        (fun _ : Quadrant => (0 : ℝ)) x := by
    intro c x
    simp
  obtain ⟨q, hq, herror⟩ :=
    exists_uniform_dyadic_quadrant_grid_shape_error
      (fun _ : Quadrant => (0 : ℝ)) hzero hzero_hom ε hε
  refine ⟨q, hq, ?_⟩
  intro k z hzlo hzhi
  have h := herror k z hzlo hzhi
  simpa using h

example (ε : ℝ) (hε : 0 < ε) :
    (let gfun : Quadrant → ℝ := fun x => -(x.1 : ℝ) + 3 * (x.2 : ℝ)
    ∃ q : ℕ, 4 ≤ q ∧ ∀ k : ℕ, ∀ z : ℕ × ℕ,
      q * 2 ^ k ≤ z.1 + z.2 → z.1 + z.2 < 2 * (q * 2 ^ k) →
      |(gfun ((z.1 : ℝ≥0), (z.2 : ℝ≥0)) -
        gfun (((2 ^ k * (z.1 / 2 ^ k) : ℕ) : ℝ≥0),
          ((2 ^ k * (z.2 / 2 ^ k) : ℕ) : ℝ≥0)))| ≤
        ε * ((z.1 + z.2 : ℕ) : ℝ)) := by
  let gfun : Quadrant → ℝ := fun x => -(x.1 : ℝ) + 3 * (x.2 : ℝ)
  change
    ∃ q : ℕ, 4 ≤ q ∧ ∀ k : ℕ, ∀ z : ℕ × ℕ,
      q * 2 ^ k ≤ z.1 + z.2 → z.1 + z.2 < 2 * (q * 2 ^ k) →
      |(gfun ((z.1 : ℝ≥0), (z.2 : ℝ≥0)) -
        gfun (((2 ^ k * (z.1 / 2 ^ k) : ℕ) : ℝ≥0),
          ((2 ^ k * (z.2 / 2 ^ k) : ℕ) : ℝ≥0)))| ≤
        ε * ((z.1 + z.2 : ℕ) : ℝ)
  let gfun : Quadrant → ℝ := fun x => -(x.1 : ℝ) + 3 * (x.2 : ℝ)
  have hg : Continuous gfun := by fun_prop
  have hhom : ∀ (c : ℝ≥0) (x : Quadrant), gfun (c • x) = (c : ℝ) * gfun x := by
    intro c x
    change -((c * x.1 : ℝ≥0) : ℝ) + 3 * ((c * x.2 : ℝ≥0) : ℝ) =
      (c : ℝ) * (-(x.1 : ℝ) + 3 * (x.2 : ℝ))
    simp only [NNReal.coe_mul]
    ring
  exact exists_uniform_dyadic_quadrant_grid_shape_error gfun hg hhom ε hε

end LPPDifferentiability
