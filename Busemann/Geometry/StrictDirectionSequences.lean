/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Frozen.Definitions.InteriorDirection
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Tactic

/-! Explicit strict comparison directions in the interior unit segment. -/

@[expose] public section

open Filter LPPDifferentiability
open scoped NNReal Topology

namespace LPP.Busemann

/-- Every interior direction has sequences approaching it strictly from each
side. These elementary comparison directions supply the countable bracketing
in GRS arXiv:1510.00859v2, Theorem 6.1, Step 2, and JR arXiv:1810.03580v3,
Theorem 4.16. The perturbations stay in the literal interior unit segment. -/
theorem exists_strict_left_right_direction_sequences (ξ : InteriorDirection) :
    ∃ left right : ℕ → InteriorDirection,
      (∀ n, (left n).1.1 < ξ.1.1 ∧ ξ.1.1 < (right n).1.1) ∧
      Tendsto left atTop (𝓝 ξ) ∧ Tendsto right atTop (𝓝 ξ) := by
  let x : ℝ := ξ.1.1
  let y : ℝ := ξ.1.2
  have hx : 0 < x := NNReal.coe_pos.mpr ξ.2.1
  have hy : 0 < y := NNReal.coe_pos.mpr ξ.2.2.1
  have hsum : x + y = 1 := ξ.2.2.2
  let t : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2)
  have ht (n : ℕ) : 0 < t n ∧ t n < 1 := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hden : (0 : ℝ) < (n : ℝ) + 2 := by linarith only [hn]
    constructor
    · exact div_pos zero_lt_one hden
    · exact (div_lt_iff₀ hden).2 (by linarith only [hn])
  have hp (n : ℕ) :
      0 < (1 - t n) * x ∧ 0 < y + t n * x ∧
      0 < x + t n * y ∧ 0 < (1 - t n) * y := by
    have htn := ht n
    exact ⟨mul_pos (sub_pos.mpr htn.2) hx,
      add_pos hy (mul_pos htn.1 hx), add_pos hx (mul_pos htn.1 hy),
      mul_pos (sub_pos.mpr htn.2) hy⟩
  let left : ℕ → InteriorDirection := fun n =>
    ⟨(Real.toNNReal ((1 - t n) * x), Real.toNNReal (y + t n * x)),
      ⟨Real.toNNReal_pos.mpr (hp n).1, Real.toNNReal_pos.mpr (hp n).2.1, by
        rw [Real.coe_toNNReal _ (hp n).1.le, Real.coe_toNNReal _ (hp n).2.1.le]
        nlinarith only [hsum]⟩⟩
  let right : ℕ → InteriorDirection := fun n =>
    ⟨(Real.toNNReal (x + t n * y), Real.toNNReal ((1 - t n) * y)),
      ⟨Real.toNNReal_pos.mpr (hp n).2.2.1, Real.toNNReal_pos.mpr (hp n).2.2.2, by
        rw [Real.coe_toNNReal _ (hp n).2.2.1.le, Real.coe_toNNReal _ (hp n).2.2.2.le]
        nlinarith only [hsum]⟩⟩
  have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_mono (fun _ => le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 2))
      tendsto_natCast_atTop_atTop
  have htlim : Tendsto t atTop (𝓝 0) := by
    simpa only [t, one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hnat
  have hl1 : Tendsto (fun n => (1 - t n) * x) atTop (𝓝 x) := by
    simpa only [sub_zero, one_mul] using
      ((tendsto_const_nhds (x := (1 : ℝ))).sub htlim).mul (tendsto_const_nhds (x := x))
  have hl2 : Tendsto (fun n => y + t n * x) atTop (𝓝 y) := by
    simpa only [zero_mul, add_zero] using
      (tendsto_const_nhds (x := y)).add (htlim.mul (tendsto_const_nhds (x := x)))
  have hr1 : Tendsto (fun n => x + t n * y) atTop (𝓝 x) := by
    simpa only [zero_mul, add_zero] using
      (tendsto_const_nhds (x := x)).add (htlim.mul (tendsto_const_nhds (x := y)))
  have hr2 : Tendsto (fun n => (1 - t n) * y) atTop (𝓝 y) := by
    simpa only [sub_zero, one_mul] using
      ((tendsto_const_nhds (x := (1 : ℝ))).sub htlim).mul (tendsto_const_nhds (x := y))
  have hl1N : Tendsto (fun n => (left n).1.1) atTop (𝓝 ξ.1.1) := by
    simpa only [left, x, Real.toNNReal_coe, Function.comp_def] using
      (continuous_real_toNNReal.tendsto x).comp hl1
  have hl2N : Tendsto (fun n => (left n).1.2) atTop (𝓝 ξ.1.2) := by
    simpa only [left, y, Real.toNNReal_coe, Function.comp_def] using
      (continuous_real_toNNReal.tendsto y).comp hl2
  have hr1N : Tendsto (fun n => (right n).1.1) atTop (𝓝 ξ.1.1) := by
    simpa only [right, x, Real.toNNReal_coe, Function.comp_def] using
      (continuous_real_toNNReal.tendsto x).comp hr1
  have hr2N : Tendsto (fun n => (right n).1.2) atTop (𝓝 ξ.1.2) := by
    simpa only [right, y, Real.toNNReal_coe, Function.comp_def] using
      (continuous_real_toNNReal.tendsto y).comp hr2
  refine ⟨left, right, ?_, tendsto_subtype_rng.mpr (hl1N.prodMk_nhds hl2N),
    tendsto_subtype_rng.mpr (hr1N.prodMk_nhds hr2N)⟩
  intro n
  constructor
  · apply NNReal.coe_lt_coe.mp
    change (Real.toNNReal ((1 - t n) * x) : ℝ) < x
    rw [Real.coe_toNNReal _ (hp n).1.le]
    nlinarith only [mul_pos (ht n).1 hx]
  · apply NNReal.coe_lt_coe.mp
    change x < (Real.toNNReal (x + t n * y) : ℝ)
    rw [Real.coe_toNNReal _ (hp n).2.2.1.le]
    exact lt_add_of_pos_right x (mul_pos (ht n).1 hy)

end LPP.Busemann
