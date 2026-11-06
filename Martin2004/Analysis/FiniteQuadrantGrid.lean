/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.Quadrant
public import Mathlib.Topology.UniformSpace.HeineCantor

import Mathlib.Tactic

/-!
# Finite lower grids in the closed quadrant

The reciprocal integer mesh includes zero and one. Rounding down preserves
coordinate order and gives the two floor-site errors in the finite-grid
argument in the proof of Martin (2004), Lemma 5.4, for bounded expected
passage values.
-/

public section

open Set Filter
open scoped Topology NNReal

namespace LPPDifferentiability

/-- Each point in the closed unit interval has a lower reciprocal-mesh point,
including both endpoints, with error strictly below one mesh width. -/
theorem exists_lower_unit_mesh (k : ℕ) (hk : 0 < k)
    (x : ℝ≥0) (hx : x ≤ 1) :
    ∃ i : Fin (k + 1),
      (i.val : ℝ≥0) / (k : ℝ≥0) ≤ x ∧
      (x : ℝ) - (i.val : ℝ) / (k : ℝ) < 1 / (k : ℝ) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hnonneg : 0 ≤ (k : ℝ) * (x : ℝ) := mul_nonneg hkR.le x.coe_nonneg
  let j := ⌊(k : ℝ) * (x : ℝ)⌋₊
  have hj : j ≤ k := by
    apply Nat.floor_le_of_le
    have hxR : (x : ℝ) ≤ 1 := by exact_mod_cast hx
    nlinarith only [hxR, hkR]
  refine ⟨⟨j, Nat.lt_succ_of_le hj⟩, ?_, ?_⟩
  · apply (NNReal.coe_le_coe).mp
    change (j : ℝ) / (k : ℝ) ≤ (x : ℝ)
    apply (div_le_iff₀ hkR).mpr
    exact (Nat.floor_le hnonneg).trans_eq (mul_comm (k : ℝ) (x : ℝ))
  · change (x : ℝ) - (j : ℝ) / (k : ℝ) < 1 / (k : ℝ)
    apply (lt_div_iff₀ hkR).mpr
    have hf := Nat.lt_floor_add_one ((k : ℝ) * (x : ℝ))
    rw [sub_mul, div_mul_cancel₀ _ hkR.ne']
    change (k : ℝ) * (x : ℝ) < (j : ℝ) + 1 at hf
    nlinarith only [hf]

/-- Uniform continuity on the closed unit square supplies a common
modulus for the same continuous quadrant function. -/
theorem continuous_quadrant_unit_square_modulus (g : Quadrant → ℝ)
    (hg : Continuous g) {a : ℝ} (ha : 0 < a) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x y : Quadrant,
      x ≤ (1, 1) → y ≤ (1, 1) → dist x y < δ → |g x - g y| < a := by
  have hc : IsCompact (Icc (0 : Quadrant) (1, 1)) := isCompact_Icc
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp
    (hc.uniformContinuousOn_of_continuous hg.continuousOn) a ha
  refine ⟨δ, hδ, ?_⟩
  intro x y hx hy hxy
  exact hmod x ⟨bot_le, hx⟩ y ⟨bot_le, hy⟩ hxy

/-- A finite lower grid turns the pointwise floor limits of one continuous,
homogeneous function into uniform lattice approximation. The displacement
bound is the deterministic form of finite expected concatenation. -/
theorem uniform_lattice_approximation_of_finite_lower_grid
    (F : (ℕ × ℕ) → ℝ) (g : Quadrant → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hstep : ∀ d z : ℕ × ℕ, d.1 ≤ z.1 → d.2 ≤ z.2 →
      F d - L * (((z.1 - d.1) + (z.2 - d.2) : ℕ) : ℝ) ≤ F z)
    (hlim : ∀ x : Quadrant, Tendsto (fun n : ℕ =>
      F (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) /
        (n : ℝ)) atTop (𝓝 (g x)))
    (hcont : Continuous g)
    (hhom : ∀ (c : ℝ≥0) (x : Quadrant), g (c • x) = (c : ℝ) * g x)
    (hupper : ∀ z : ℕ × ℕ, F z ≤ g ((z.1 : ℝ≥0), (z.2 : ℝ≥0))) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 0 < N ∧ ∀ z : ℕ × ℕ,
      N ≤ z.1 + z.2 →
      |F z - g ((z.1 : ℝ≥0), (z.2 : ℝ≥0))| <
        ε * ((z.1 + z.2 : ℕ) : ℝ) := by
  intro ε hε
  let a := ε / 8
  have ha : 0 < a := div_pos hε (by norm_num)
  obtain ⟨δ, hδ, hmod⟩ := continuous_quadrant_unit_square_modulus g hcont ha
  have hmesh : 0 < min δ (a / (L + 1)) :=
    lt_min hδ (div_pos ha (by linarith only [hL]))
  obtain ⟨k₀, hk₀⟩ := exists_nat_one_div_lt hmesh
  let k := k₀ + 1
  have hk : 0 < k := Nat.succ_pos _
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hkmesh : 1 / (k : ℝ) < min δ (a / (L + 1)) := by
    simpa only [k, Nat.cast_add, Nat.cast_one] using hk₀
  have hku : 1 / (k : ℝ) < δ := lt_of_lt_of_le hkmesh (min_le_left _ _)
  have hkLa : L * (1 / (k : ℝ)) < a := by
    have hsmall : 1 / (k : ℝ) < a / (L + 1) :=
      lt_of_lt_of_le hkmesh (min_le_right _ _)
    have hpos : 0 < 1 / (k : ℝ) := one_div_pos.mpr hkR
    have hh := (lt_div_iff₀ (by linarith only [hL] : 0 < L + 1)).mp hsmall
    nlinarith only [hh, hpos]
  let grid (i : Fin (k + 1) × Fin (k + 1)) : Quadrant :=
    ((i.1.val : ℝ≥0) / (k : ℝ≥0), (i.2.val : ℝ≥0) / (k : ℝ≥0))
  have hfinite : ∀ᶠ n : ℕ in atTop, ∀ i : Fin (k + 1) × Fin (k + 1),
      g (grid i) - a <
        F (⌊(n : ℝ) * ((grid i).1 : ℝ)⌋₊,
          ⌊(n : ℝ) * ((grid i).2 : ℝ)⌋₊) / (n : ℝ) := by
    apply Filter.eventually_all.mpr
    intro i
    exact (tendsto_order.mp (hlim (grid i))).1 _ (sub_lt_self _ ha)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hfinite
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (2 * L / a)
  let M := max (max N₀ N₁) 1
  refine ⟨2 * M, by dsimp [M]; omega, ?_⟩
  intro z hz
  let m := max z.1 z.2
  have hlen : z.1 + z.2 ≤ 2 * m := by dsimp [m]; omega
  have hmM : M ≤ m := by omega
  have hmN : N₀ ≤ m := le_trans (le_trans (le_max_left N₀ N₁) (le_max_left (max N₀ N₁) 1)) hmM
  have hmN₁ : N₁ ≤ m := le_trans (le_trans (le_max_right N₀ N₁) (le_max_left (max N₀ N₁) 1)) hmM
  have hm : 0 < m := by dsimp [M] at hmM; omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmNN : (m : ℝ≥0) ≠ 0 := by exact_mod_cast hm.ne'
  have htail : 2 * L < (m : ℝ) * a := by
    have hmn : (N₁ : ℝ) ≤ m := by exact_mod_cast hmN₁
    have hdiv : 2 * L / a < (m : ℝ) := lt_of_lt_of_le hN₁ hmn
    exact (div_lt_iff₀ ha).mp hdiv
  let x : Quadrant := ((z.1 : ℝ≥0) / (m : ℝ≥0),
    (z.2 : ℝ≥0) / (m : ℝ≥0))
  have hx₁ : x.1 ≤ 1 := by
    change (z.1 : ℝ≥0) / (m : ℝ≥0) ≤ 1
    apply (div_le_one₀ (by exact_mod_cast hm)).mpr
    exact_mod_cast le_max_left z.1 z.2
  have hx₂ : x.2 ≤ 1 := by
    change (z.2 : ℝ≥0) / (m : ℝ≥0) ≤ 1
    apply (div_le_one₀ (by exact_mod_cast hm)).mpr
    exact_mod_cast le_max_right z.1 z.2
  obtain ⟨i, hi, hei⟩ := exists_lower_unit_mesh k hk x.1 hx₁
  obtain ⟨j, hj, hej⟩ := exists_lower_unit_mesh k hk x.2 hx₂
  let y := grid (i, j)
  have hyx : y ≤ x := ⟨hi, hj⟩
  have hy : y ≤ (1, 1) := le_trans hyx ⟨hx₁, hx₂⟩
  have he₁ : (x.1 : ℝ) - (y.1 : ℝ) < 1 / (k : ℝ) := hei
  have he₂ : (x.2 : ℝ) - (y.2 : ℝ) < 1 / (k : ℝ) := hej
  have hxy : dist x y < δ := by
    rw [Prod.dist_eq, max_lt_iff]
    constructor
    · rw [NNReal.dist_eq]
      rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hi))]
      exact lt_trans he₁ hku
    · rw [NNReal.dist_eq]
      rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hj))]
      exact lt_trans he₂ hku
  have hgxy : g x - g y < a :=
    (abs_lt.mp (hmod x y ⟨hx₁, hx₂⟩ hy hxy)).2
  have hxmul₁ : (m : ℝ) * (x.1 : ℝ) = (z.1 : ℝ) := by
    change (m : ℝ) * ((z.1 : ℝ) / (m : ℝ)) = (z.1 : ℝ)
    exact mul_div_cancel₀ _ hmR.ne'
  have hxmul₂ : (m : ℝ) * (x.2 : ℝ) = (z.2 : ℝ) := by
    change (m : ℝ) * ((z.2 : ℝ) / (m : ℝ)) = (z.2 : ℝ)
    exact mul_div_cancel₀ _ hmR.ne'
  have hscale : (m : ℝ≥0) • x = ((z.1 : ℝ≥0), (z.2 : ℝ≥0)) := by
    apply Prod.ext
    · change (m : ℝ≥0) * ((z.1 : ℝ≥0) / (m : ℝ≥0)) = _
      exact mul_div_cancel₀ _ hmNN
    · change (m : ℝ≥0) * ((z.2 : ℝ≥0) / (m : ℝ≥0)) = _
      exact mul_div_cancel₀ _ hmNN
  have hgscale : g ((z.1 : ℝ≥0), (z.2 : ℝ≥0)) = (m : ℝ) * g x := by
    rw [← hscale, hhom]
    simp only [NNReal.coe_natCast]
  let d : ℕ × ℕ := (⌊(m : ℝ) * (y.1 : ℝ)⌋₊,
    ⌊(m : ℝ) * (y.2 : ℝ)⌋₊)
  have hd₁ : d.1 ≤ z.1 := by
    apply Nat.floor_le_of_le
    calc (m : ℝ) * (y.1 : ℝ) ≤ (m : ℝ) * (x.1 : ℝ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hi) hmR.le
      _ = _ := hxmul₁
  have hd₂ : d.2 ≤ z.2 := by
    apply Nat.floor_le_of_le
    calc (m : ℝ) * (y.2 : ℝ) ≤ (m : ℝ) * (x.2 : ℝ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hj) hmR.le
      _ = _ := hxmul₂
  have hround : (((z.1 - d.1) + (z.2 - d.2) : ℕ) : ℝ) <
      (m : ℝ) * (2 * (1 / (k : ℝ))) + 2 := by
    rw [Nat.cast_add, Nat.cast_sub hd₁, Nat.cast_sub hd₂]
    have hf₁ := Nat.lt_floor_add_one ((m : ℝ) * (y.1 : ℝ))
    have hf₂ := Nat.lt_floor_add_one ((m : ℝ) * (y.2 : ℝ))
    change (m : ℝ) * (y.1 : ℝ) < (d.1 : ℝ) + 1 at hf₁
    change (m : ℝ) * (y.2 : ℝ) < (d.2 : ℝ) + 1 at hf₂
    have he := mul_lt_mul_of_pos_left (add_lt_add he₁ he₂) hmR
    nlinarith only [hf₁, hf₂, he, hxmul₁, hxmul₂]
  have hroundL : L * (((z.1 - d.1) + (z.2 - d.2) : ℕ) : ℝ) <
      3 * (m : ℝ) * a := by
    have hr := mul_le_mul_of_nonneg_left hround.le hL
    have hmeshL := mul_lt_mul_of_pos_left hkLa (by linarith only [hmR] : 0 < 2 * (m : ℝ))
    nlinarith only [hr, hmeshL, htail]
  have hgrid : (m : ℝ) * (g y - a) < F d := by
    have hh := hN₀ m hmN (i, j)
    change g y - a < F d / (m : ℝ) at hh
    have hh' := (lt_div_iff₀ hmR).mp hh
    nlinarith only [hh']
  have hglower := hstep d z hd₁ hd₂
  have hmodm := mul_lt_mul_of_pos_left hgxy hmR
  have herror : g ((z.1 : ℝ≥0), (z.2 : ℝ≥0)) - F z <
      ε * (m : ℝ) := by
    rw [hgscale]
    dsimp [a] at *
    nlinarith only [hgrid, hglower, hmodm, hroundL, hε, hmR]
  rw [abs_of_nonpos (sub_nonpos.mpr (hupper z))]
  have hmlen : (m : ℝ) ≤ ((z.1 + z.2 : ℕ) : ℝ) := by
    exact_mod_cast (show m ≤ z.1 + z.2 by dsimp [m]; omega)
  have hfinal := herror.trans_le (mul_le_mul_of_nonneg_left hmlen hε.le)
  linarith only [hfinal]

end LPPDifferentiability
