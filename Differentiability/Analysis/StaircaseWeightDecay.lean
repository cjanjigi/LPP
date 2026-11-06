/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Scalar decay in the staircase-weights estimate

Scalar staircase-weight estimates. These are the two scalar limits displayed in the proof of
Lemma B.6 of the differentiability preprint. They do not include the preceding denominator
comparison or probability bound.

## References

- C. Janjigian, F. Rassoul-Agha and T. Seppäläinen, *Differentiability of the shape function
  in the planar corner growth model*, preprint.
-/

public section

open Filter
open scoped Topology

namespace LPPDifferentiability

/-- The exact first scalar term in the staircase-weights proof tends to zero.
The hypotheses `1 < p` and `1 ≤ q` are not used in the proof; the combined
inequality on `K` already gives the strictly negative exponential exponent. -/
theorem staircase_weight_polynomial_decay {p q cstar Cp : ℝ} {K : ℕ}
    (_hp : 1 < p) (_hq : 1 ≤ q) (hcstar : 0 < cstar) (hCp : 0 ≤ Cp)
    (hK : 2 * q + 2 < (K : ℝ) * (p - 1)) :
    Tendsto (fun k : ℕ =>
      ((2 : ℝ) ^ k) ^ q *
        (16 * cstar * Cp * (k : ℝ) ^ 2 * ((2 : ℝ) ^ k) ^ ((1 - p) / 2)) ^ K)
      atTop (𝓝 0) := by
  let b : ℝ := ((K : ℝ) * (p - 1) / 2 - q) * Real.log 2
  have hb : 0 < b :=
    mul_pos (by linarith) (Real.log_pos (by norm_num))
  have hreal : Tendsto (fun x : ℝ =>
      x ^ (2 * K) * Real.exp (-b * x)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((2 * K : ℕ) : ℝ) b hb
  have hscaled : Tendsto (fun k : ℕ =>
      |16 * cstar * Cp| ^ K * ((k : ℝ) ^ (2 * K) * Real.exp (-b * (k : ℝ))))
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero] using
      (hreal.comp tendsto_natCast_atTop_atTop).const_mul (|16 * cstar * Cp| ^ K)
  have hconst : |16 * cstar * Cp| = 16 * cstar * Cp :=
    abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) hcstar.le) hCp)
  have hpower (k : ℕ) :
      ((2 : ℝ) ^ k) ^ q * (((2 : ℝ) ^ k) ^ ((1 - p) / 2)) ^ K =
        Real.exp (-b * (k : ℝ)) := by
    have hs : 0 < (2 : ℝ) ^ k := pow_pos zero_lt_two k
    rw [← Real.rpow_natCast (((2 : ℝ) ^ k) ^ ((1 - p) / 2)) K,
      ← Real.rpow_mul hs.le ((1 - p) / 2) (K : ℝ),
      ← Real.rpow_add hs q (((1 - p) / 2) * (K : ℝ)),
      ← Real.rpow_natCast (2 : ℝ) k,
      ← Real.rpow_mul (le_of_lt zero_lt_two) (k : ℝ)
        (q + (1 - p) / 2 * (K : ℝ)),
      Real.rpow_def_of_pos zero_lt_two]
    congr 1
    dsimp [b]
    ring
  apply hscaled.congr'
  filter_upwards with k
  rw [hconst]
  conv_rhs => rw [mul_pow, mul_pow, ← pow_mul]
  calc
    (16 * cstar * Cp) ^ K *
        ((k : ℝ) ^ (2 * K) * Real.exp (-b * (k : ℝ))) =
      (16 * cstar * Cp) ^ K * (k : ℝ) ^ (2 * K) *
        (((2 : ℝ) ^ k) ^ q * (((2 : ℝ) ^ k) ^ ((1 - p) / 2)) ^ K) := by
          rw [hpower]
          ring
    _ = ((2 : ℝ) ^ k) ^ q *
        ((16 * cstar * Cp) ^ K * (k : ℝ) ^ (2 * K) *
          (((2 : ℝ) ^ k) ^ ((1 - p) / 2)) ^ K) := by ring

private theorem dyadic_stretched_exponential_decay {q c a : ℝ}
    (hc : 0 < c) (ha : 0 < a) :
    Tendsto (fun k : ℕ =>
      ((2 : ℝ) ^ k) ^ q * Real.exp (-c * ((2 : ℝ) ^ k) ^ a))
      atTop (𝓝 0) := by
  have hinner : Tendsto (fun k : ℕ => ((2 : ℝ) ^ k) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  have hlimit :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (q / a) c hc).comp hinner
  apply hlimit.congr'
  filter_upwards with k
  have hs : 0 < (2 : ℝ) ^ k := pow_pos zero_lt_two k
  have hexponent : a * (q / a) = q := by field_simp [ne_of_gt ha]
  rw [Function.comp_apply, ← Real.rpow_mul hs.le, hexponent]

/-- The exact second scalar majorant in the staircase-weights proof tends to
zero. The hypothesis `1 ≤ q` is not used in the proof, and the limit holds for
other real `q` as well. -/
theorem staircase_weight_stretched_exponential_decay {q c epsilon : ℝ}
    (_hq : 1 ≤ q) (hc : 0 < c) (hepsilon : 0 < epsilon) :
    Tendsto (fun k : ℕ =>
      ((2 : ℝ) ^ k) ^ q *
        Real.exp (-c * ((2 : ℝ) ^ k) ^ epsilon / (k : ℝ) ^ 4))
      atTop (𝓝 0) := by
  have ha : 0 < epsilon / 2 := half_pos hepsilon
  have hb : 0 < epsilon / 2 * Real.log 2 :=
    mul_pos ha (Real.log_pos (by norm_num))
  have hpoly : Tendsto (fun k : ℕ =>
      (k : ℝ) ^ 4 * Real.exp (-(epsilon / 2 * Real.log 2) * (k : ℝ)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.rpow_ofNat] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (4 : ℝ)
        (epsilon / 2 * Real.log 2) hb).comp tendsto_natCast_atTop_atTop
  have hdyadic (k : ℕ) : ((2 : ℝ) ^ k) ^ (epsilon / 2) =
      Real.exp ((epsilon / 2 * Real.log 2) * (k : ℝ)) := by
    rw [← Real.rpow_natCast (2 : ℝ) k,
      ← Real.rpow_mul (le_of_lt zero_lt_two) (k : ℝ) (epsilon / 2),
      Real.rpow_def_of_pos zero_lt_two]
    congr 1
    ring
  have hbound : ∀ᶠ k : ℕ in atTop,
      (k : ℝ) ^ 4 ≤ ((2 : ℝ) ^ k) ^ (epsilon / 2) := by
    filter_upwards [hpoly.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with k hk
    have hs : 0 < ((2 : ℝ) ^ k) ^ (epsilon / 2) :=
      Real.rpow_pos_of_pos (pow_pos zero_lt_two k) _
    have hratio : (k : ℝ) ^ 4 / ((2 : ℝ) ^ k) ^ (epsilon / 2) < 1 := by
      rw [hdyadic k, div_eq_mul_inv, ← Real.exp_neg]
      simpa only [neg_mul] using hk
    have hlt := (div_lt_iff₀ hs).mp hratio
    simpa only [one_mul] using hlt.le
  have hupper : Tendsto (fun k : ℕ =>
      ((2 : ℝ) ^ k) ^ q * Real.exp (-c * ((2 : ℝ) ^ k) ^ (epsilon / 2)))
      atTop (𝓝 0) := dyadic_stretched_exponential_decay hc ha
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards with k
    exact mul_nonneg (Real.rpow_nonneg (pow_nonneg (by norm_num) k) q)
      (Real.exp_pos _).le
  · filter_upwards [hbound, eventually_gt_atTop (0 : ℕ)] with k hk hkpos
    have hkreal : 0 < (k : ℝ) := by exact_mod_cast hkpos
    have hs : 0 < (2 : ℝ) ^ k := pow_pos zero_lt_two k
    have hhalf : 0 < ((2 : ℝ) ^ k) ^ (epsilon / 2) :=
      Real.rpow_pos_of_pos hs _
    have hsquare : ((2 : ℝ) ^ k) ^ epsilon =
        ((2 : ℝ) ^ k) ^ (epsilon / 2) * ((2 : ℝ) ^ k) ^ (epsilon / 2) := by
      rw [← Real.rpow_add hs]
      congr 1
      ring
    have hquot : ((2 : ℝ) ^ k) ^ (epsilon / 2) ≤
        ((2 : ℝ) ^ k) ^ epsilon / (k : ℝ) ^ 4 := by
      apply (le_div_iff₀ (pow_pos hkreal 4)).mpr
      rw [hsquare]
      exact mul_le_mul_of_nonneg_left hk hhalf.le
    have hexponent : -c * ((2 : ℝ) ^ k) ^ epsilon / (k : ℝ) ^ 4 ≤
        -c * ((2 : ℝ) ^ k) ^ (epsilon / 2) := by
      simpa only [mul_div_assoc] using
        mul_le_mul_of_nonpos_left hquot (neg_nonpos.mpr hc.le)
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent)
      (Real.rpow_nonneg hs.le q)

end LPPDifferentiability
