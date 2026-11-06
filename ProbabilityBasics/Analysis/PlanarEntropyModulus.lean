/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Planar entropy and a uniform numerical boundary modulus

Elementary deterministic estimates for the planar entropy in Martin's bounded
boundary argument. Each statement writes the entropy formula out explicitly.
These results neither construct a shape function nor assert its continuity.
-/

public section

open scoped NNReal Topology

namespace LPPDifferentiability

private theorem mul_log_mul (x y : ℝ) :
    (x * y) * Real.log (x * y) =
      y * (x * Real.log x) + x * (y * Real.log y) := by
  have h := Real.negMulLog_mul x y
  simp only [Real.negMulLog] at h
  linarith only [h]

/-- The entropy vanishes on the horizontal axis, including the origin. -/
@[simp] theorem planar_entropy_zero_right (h : ℝ≥0) :
    ((h : ℝ) + 0) * Real.log ((h : ℝ) + 0) -
      (h : ℝ) * Real.log h - 0 * Real.log 0 = 0 := by
  simp only [add_zero, zero_mul, sub_self]

/-- The entropy vanishes on the vertical axis, including the origin. -/
@[simp] theorem planar_entropy_zero_left (t : ℝ≥0) :
    (0 + (t : ℝ)) * Real.log (0 + (t : ℝ)) -
      0 * Real.log 0 - (t : ℝ) * Real.log t = 0 := by
  simp only [zero_add, zero_mul, sub_zero, sub_self]

/-- The planar entropy is nonnegative on the closed quadrant. -/
theorem planar_entropy_nonneg (h t : ℝ≥0) :
    0 ≤ ((h : ℝ) + t) * Real.log ((h : ℝ) + t) -
      (h : ℝ) * Real.log h - (t : ℝ) * Real.log t := by
  by_cases hh : h = 0
  · subst h
    simp only [NNReal.coe_zero, zero_add, zero_mul, sub_zero, sub_self, le_refl]
  by_cases ht : t = 0
  · subst t
    simp only [NNReal.coe_zero, add_zero, zero_mul, sub_self, le_refl]
  have hh' : 0 < (h : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hh)
  have ht' : 0 < (t : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ht)
  have ha := Real.log_le_log hh' (le_add_of_nonneg_right t.coe_nonneg)
  have hb := Real.log_le_log ht' (le_add_of_nonneg_left h.coe_nonneg)
  have hc := mul_nonneg h.coe_nonneg (sub_nonneg.mpr ha)
  have hd := mul_nonneg t.coe_nonneg (sub_nonneg.mpr hb)
  nlinarith only [hc, hd]

/-- Degree-one homogeneity, also when the scale or either coordinate is zero. -/
theorem planar_entropy_mul (c h t : ℝ≥0) :
    (((c * h : ℝ≥0) : ℝ) + (c * t : ℝ≥0)) *
        Real.log (((c * h : ℝ≥0) : ℝ) + (c * t : ℝ≥0)) -
      (c * h : ℝ≥0) * Real.log (c * h : ℝ≥0) -
      (c * t : ℝ≥0) * Real.log (c * t : ℝ≥0) =
    (c : ℝ) * (((h : ℝ) + t) * Real.log ((h : ℝ) + t) -
      (h : ℝ) * Real.log h - (t : ℝ) * Real.log t) := by
  simp only [NNReal.coe_mul, ← mul_add]
  rw [mul_log_mul, mul_log_mul, mul_log_mul]
  ring

/-- Continuity includes both axes under the total real logarithm convention. -/
theorem continuous_planar_entropy :
    Continuous (fun p : ℝ≥0 × ℝ≥0 =>
      ((p.1 : ℝ) + p.2) * Real.log ((p.1 : ℝ) + p.2) -
        (p.1 : ℝ) * Real.log p.1 - (p.2 : ℝ) * Real.log p.2) := by
  exact ((Real.continuous_mul_log.comp
    ((NNReal.continuous_coe.comp continuous_fst).add
      (NNReal.continuous_coe.comp continuous_snd))).sub
        (Real.continuous_mul_log.comp
          (NNReal.continuous_coe.comp continuous_fst))).sub
            (Real.continuous_mul_log.comp
              (NNReal.continuous_coe.comp continuous_snd))

/-- An entropy bound independent of the second coordinate within a bounded face. -/
theorem planar_entropy_le (h t : ℝ≥0) (R : ℝ) (hR : 0 < R)
    (hh : 0 < h) (ht : (t : ℝ) ≤ R) :
    ((h : ℝ) + t) * Real.log ((h : ℝ) + t) -
        (h : ℝ) * Real.log h - (t : ℝ) * Real.log t ≤
      (h : ℝ) * Real.log (1 + R / h) + h := by
  have hh' : 0 < (h : ℝ) := NNReal.coe_pos.mpr hh
  by_cases ht0 : t = 0
  · subst t
    simp only [NNReal.coe_zero, add_zero, zero_mul, sub_self]
    exact add_nonneg (mul_nonneg h.coe_nonneg
      (Real.log_nonneg (le_add_of_nonneg_right
        (div_nonneg hR.le h.coe_nonneg)))) h.coe_nonneg
  have ht' : 0 < (t : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ht0)
  have hs : 0 < (h : ℝ) + t := add_pos hh' ht'
  have hf : ((h : ℝ) + t) / h ≤ 1 + R / h := by
    rw [add_div, div_self hh'.ne']
    linarith only [div_le_div_of_nonneg_right ht hh'.le]
  have hf' := mul_le_mul_of_nonneg_left
    (Real.log_le_log (div_pos hs hh') hf) h.coe_nonneg
  have hg := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hs ht')) t.coe_nonneg
  have he : (t : ℝ) * (((h : ℝ) + t) / t - 1) = h := by
    field_simp
    ring
  rw [he] at hg
  rw [Real.log_div hs.ne' hh'.ne'] at hf'
  rw [Real.log_div hs.ne' ht'.ne'] at hg
  nlinarith only [hf', hg]

private theorem mul_log_one_add_div_eq (h : ℝ≥0) (R : ℝ) (hR : 0 < R) :
    (h : ℝ) * Real.log (1 + R / h) =
      (h : ℝ) * Real.log ((h : ℝ) + R) - (h : ℝ) * Real.log h := by
  by_cases hh : h = 0
  · subst h
    simp only [NNReal.coe_zero, zero_mul, sub_zero]
  have hh' : 0 < (h : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hh)
  have he : 1 + R / (h : ℝ) = ((h : ℝ) + R) / h := by
    rw [add_div, div_self hh'.ne']
  rw [he, Real.log_div (add_pos hh' hR).ne' hh'.ne']
  ring

private theorem continuous_mul_log_one_add_div (R : ℝ) (hR : 0 < R) :
    Continuous (fun h : ℝ≥0 => (h : ℝ) * Real.log (1 + R / h)) := by
  have he : (fun h : ℝ≥0 => (h : ℝ) * Real.log (1 + R / h)) =
      (fun h : ℝ≥0 => (h : ℝ) * Real.log ((h : ℝ) + R) -
        (h : ℝ) * Real.log h) := by
    funext h
    exact mul_log_one_add_div_eq h R hR
  rw [he]
  refine (NNReal.continuous_coe.mul
    ((NNReal.continuous_coe.add continuous_const).log ?_)).sub
      (Real.continuous_mul_log.comp NNReal.continuous_coe)
  intro h
  exact (add_pos_of_nonneg_of_pos h.coe_nonneg hR).ne'

/-- The numerical boundary modulus is continuous, including at zero.
The statement also allows a signed `L`. -/
theorem continuous_planar_boundary_modulus (L R : ℝ) (hR : 0 < R) :
    Continuous (fun h : ℝ≥0 => (h : ℝ) * L +
      8 * L * Real.sqrt (((h : ℝ) + R) *
        ((h : ℝ) * Real.log (1 + R / h) + h))) := by
  exact (NNReal.continuous_coe.mul continuous_const).add
    (continuous_const.mul (((NNReal.continuous_coe.add continuous_const).mul
      ((continuous_mul_log_one_add_div R hR).add NNReal.continuous_coe)).sqrt))

/-- The formula has value zero at zero; no piecewise value is assigned. -/
@[simp] theorem planar_boundary_modulus_zero (L R : ℝ) :
    (0 : ℝ) * L + 8 * L * Real.sqrt ((0 + R) *
      (0 * Real.log (1 + R / 0) + 0)) = 0 := by
  simp only [zero_mul, add_zero, mul_zero, Real.sqrt_zero]

/-- The numerical modulus tends to zero along the closed nonnegative axis. -/
theorem tendsto_planar_boundary_modulus_zero (L R : ℝ) (hR : 0 < R) :
    Filter.Tendsto (fun h : ℝ≥0 => (h : ℝ) * L +
      8 * L * Real.sqrt (((h : ℝ) + R) *
        ((h : ℝ) * Real.log (1 + R / h) + h))) (𝓝 0) (𝓝 0) := by
  simpa only [NNReal.coe_zero, zero_mul, add_zero, mul_zero, Real.sqrt_zero] using
    (continuous_planar_boundary_modulus L R hR).continuousAt.tendsto (x := 0)

/-- Monotonicity of the square root transfers the entropy bound to the
uniform numerical modulus. All endpoints are included. -/
theorem planar_boundary_le_modulus (L R : ℝ) (hL : 0 ≤ L) (hR : 0 < R)
    (h t : ℝ≥0) (ht : (t : ℝ) ≤ R) :
    (h : ℝ) * L + 8 * L * Real.sqrt (((h : ℝ) + t) *
      (((h : ℝ) + t) * Real.log ((h : ℝ) + t) -
        (h : ℝ) * Real.log h - (t : ℝ) * Real.log t)) ≤
    (h : ℝ) * L + 8 * L * Real.sqrt (((h : ℝ) + R) *
      ((h : ℝ) * Real.log (1 + R / h) + h)) := by
  by_cases hh : h = 0
  · subst h
    simp only [NNReal.coe_zero, zero_add, zero_mul, sub_zero, sub_self,
      mul_zero, add_zero, Real.sqrt_zero, le_refl]
  have he := planar_entropy_le h t R hR (pos_iff_ne_zero.mpr hh) ht
  have hs : (h : ℝ) + t ≤ (h : ℝ) + R := by linarith only [ht]
  have hp := mul_le_mul hs he
    (planar_entropy_nonneg h t) (by positivity : 0 ≤ (h : ℝ) + R)
  exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hp)
    (mul_nonneg (by norm_num) hL))

/-- For each error there is one positive radius with a closed upper endpoint. -/
theorem exists_planar_boundary_modulus_delta (L R : ℝ) (hR : 0 < R)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∀ h : ℝ≥0, h ≤ δ →
      (h : ℝ) * L + 8 * L * Real.sqrt (((h : ℝ) + R) *
        ((h : ℝ) * Real.log (1 + R / h) + h)) < ε := by
  obtain ⟨d, hd, hb⟩ := Metric.continuousAt_iff.mp
    (continuous_planar_boundary_modulus L R hR).continuousAt ε hε
  refine ⟨⟨d / 2, (half_pos hd).le⟩, NNReal.coe_pos.mp (half_pos hd), ?_⟩
  intro h hh
  have hdist : dist h 0 < d := by
    rw [NNReal.dist_eq, NNReal.coe_zero, sub_zero, abs_of_nonneg h.coe_nonneg]
    exact lt_of_le_of_lt (NNReal.coe_le_coe.mpr hh) (half_lt_self hd)
  have hv := hb hdist
  simp only [NNReal.coe_zero, zero_mul, add_zero, mul_zero, Real.sqrt_zero,
    Real.dist_eq, sub_zero] at hv
  exact (le_abs_self _).trans_lt hv

/-- A single radius controls the entropy expression for every `t≤R`. -/
theorem exists_planar_boundary_delta (L R : ℝ) (hL : 0 ≤ L) (hR : 0 < R)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∀ h : ℝ≥0, h ≤ δ → ∀ t : ℝ≥0,
      (t : ℝ) ≤ R →
      (h : ℝ) * L + 8 * L * Real.sqrt (((h : ℝ) + t) *
        (((h : ℝ) + t) * Real.log ((h : ℝ) + t) -
          (h : ℝ) * Real.log h - (t : ℝ) * Real.log t)) < ε := by
  obtain ⟨δ, hδ, hb⟩ := exists_planar_boundary_modulus_delta L R hR ε hε
  exact ⟨δ, hδ, fun h hh t ht =>
    (planar_boundary_le_modulus L R hL hR h t ht).trans_lt (hb h hh)⟩

end LPPDifferentiability
