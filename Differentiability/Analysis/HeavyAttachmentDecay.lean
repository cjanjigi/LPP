/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Analysis.HeavyAttachmentParameters
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Heavy attachment decay estimates

Deterministic power, weight-budget, and failure-term estimates for the
attachment argument.
-/

public section

open Filter
open scoped Topology

namespace LPPDifferentiability

/-- The heavy power factor is bounded by the required inverse square. -/
theorem heavy_attachment_power_bound (p kappa C_p s : ℝ) (K : ℕ)
    (hK : 4 ≤ (K : ℝ) * (p - 1))
    (hkappa : 0 < kappa) (hC_p : 0 ≤ C_p) (hs : 1 ≤ s) :
    ((4 * kappa * C_p) * s ^ ((1 - p) / 2)) ^ K ≤
      (4 * kappa * C_p) ^ K * s ^ (-2 : ℝ) := by
  have hbase : 0 ≤ 4 * kappa * C_p := by positivity
  have hs0 : 0 ≤ s := le_trans (by norm_num : (0 : ℝ) ≤ 1) hs
  have hexponent : ((1 - p) / 2) * (K : ℝ) ≤ -2 := by
    nlinarith [hK]
  have hscale : s ^ (((1 - p) / 2) * (K : ℝ)) ≤ s ^ (-2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) hexponent
  calc
    ((4 * kappa * C_p) * s ^ ((1 - p) / 2)) ^ K =
        (4 * kappa * C_p) ^ K * (s ^ ((1 - p) / 2)) ^ K := by rw [mul_pow]
    _ = (4 * kappa * C_p) ^ K * s ^ (((1 - p) / 2) * (K : ℝ)) := by
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs0]
    _ ≤ (4 * kappa * C_p) ^ K * s ^ (-2 : ℝ) :=
      mul_le_mul_of_nonneg_left hscale (pow_nonneg hbase _)

/-- The attachment weights fit in one quarter of the budget
after the stated parameter cutoff. -/
theorem heavy_attachment_weight_budget (C₁ eta kappa : ℝ) (K : ℕ) (s : ℝ)
    (hC₁ : 0 ≤ C₁) (heta : 0 < eta) (hK : 2 ≤ K)
    (hkappa : 0 < kappa)
    (hscale : kappa ≤ eta / (16 * C₁ + 16))
    (hcutoff : max 1 (128 * C₁ / eta) ≤ s) :
    2 * C₁ * (Nat.ceil (kappa * s) : ℝ) +
        ((K : ℝ) - 1) * (eta * s / (64 * (K : ℝ))) +
        eta * s / 16 ≤ eta * s / 4 := by
  have hs : 1 ≤ s := le_trans (le_max_left _ _) hcutoff
  have hs0 : 0 ≤ s := le_trans (by norm_num : (0 : ℝ) ≤ 1) hs
  have hkappa0 : 0 ≤ kappa := hkappa.le
  have hm : (Nat.ceil (kappa * s) : ℝ) ≤ kappa * s + 1 :=
    (Nat.ceil_lt_add_one (mul_nonneg hkappa0 hs0)).le
  have hscale' : kappa * (16 * C₁ + 16) ≤ eta :=
    (le_div_iff₀ (by positivity : 0 < 16 * C₁ + 16)).mp hscale
  have hkappaC₁ : 2 * C₁ * kappa ≤ eta / 8 := by
    nlinarith [hscale']
  have hcutoff' : 128 * C₁ / eta ≤ s := le_trans (le_max_right _ _) hcutoff
  have hsmall : 2 * C₁ ≤ eta * s / 64 := by
    have hmul : 128 * C₁ ≤ eta * s := by
      have hmul' := (div_le_iff₀ heta).mp hcutoff'
      nlinarith [hmul']
    nlinarith
  have hfirst :
      2 * C₁ * (Nat.ceil (kappa * s) : ℝ) ≤ 9 * (eta * s) / 64 := by
    have hceilmul :
        2 * C₁ * (Nat.ceil (kappa * s) : ℝ) ≤
          2 * C₁ * (kappa * s + 1) :=
      mul_le_mul_of_nonneg_left hm (mul_nonneg (by norm_num) hC₁)
    have hlarge : 2 * C₁ * kappa * s ≤ eta * s / 8 := by
      calc
        2 * C₁ * kappa * s ≤ (eta / 8) * s :=
          mul_le_mul_of_nonneg_right hkappaC₁ hs0
        _ = eta * s / 8 := by ring
    calc
      2 * C₁ * (Nat.ceil (kappa * s) : ℝ) ≤
          2 * C₁ * (kappa * s + 1) := hceilmul
      _ = 2 * C₁ * kappa * s + 2 * C₁ := by ring
      _ ≤ eta * s / 8 + eta * s / 64 := add_le_add hlarge hsmall
      _ = 9 * (eta * s) / 64 := by ring
  have hKtwoReal : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hKpos : 0 < (K : ℝ) := by linarith
  have hKminus : 0 ≤ (K : ℝ) - 1 := by linarith
  have hterm :
      ((K : ℝ) - 1) * (eta * s / (64 * (K : ℝ))) ≤ eta * s / 64 := by
    have hTnonneg : 0 ≤ eta * s / (64 * (K : ℝ)) := by positivity
    calc
      ((K : ℝ) - 1) * (eta * s / (64 * (K : ℝ))) ≤
          (K : ℝ) * (eta * s / (64 * (K : ℝ))) :=
        mul_le_mul_of_nonneg_right (by linarith) hTnonneg
      _ = eta * s / 64 := by
        field_simp [ne_of_gt hKpos]
  calc
    2 * C₁ * (Nat.ceil (kappa * s) : ℝ) +
        ((K : ℝ) - 1) * (eta * s / (64 * (K : ℝ))) +
        eta * s / 16 ≤ 9 * (eta * s) / 64 + eta * s / 64 + eta * s / 16 := by
      exact add_le_add (add_le_add hfirst hterm) le_rfl
    _ = 14 * (eta * s) / 64 := by ring
    _ ≤ eta * s / 4 := by nlinarith [mul_nonneg heta.le hs0]

/-- The deterministic polynomial-exponential failure term in the attachment argument tends
to zero for every fixed coefficient and positive exponential rate. -/
theorem tendsto_heavy_attachment_failure_term
    (p kappa C_p c D : ℝ) (K : ℕ)
    (hp : 1 < p) (hc : 0 < c) :
    Tendsto
      (fun s : ℝ => (D * s + 1) *
        ((4 * kappa * C_p) ^ K * s ^ (-2 : ℝ) +
          Real.exp (-c * s ^ ((p - 1) / (2 * p)))))
      atTop (𝓝 0) := by
  let epsilon : ℝ := (p - 1) / (2 * p)
  let q : ℝ := 1 / epsilon
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    exact heavy_attachment_epsilon_pos p hp
  have hscale : Tendsto (fun s : ℝ => s ^ epsilon) atTop atTop :=
    tendsto_rpow_atTop hepsilon
  have hlinear_exp_x : Tendsto
      (fun x : ℝ => x ^ q * Real.exp (-c * x)) atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero q c hc
  have hlinear_exp : Tendsto
      (fun s : ℝ => s * Real.exp (-c * s ^ epsilon)) atTop (𝓝 0) := by
    have hcomp := hlinear_exp_x.comp hscale
    apply Tendsto.congr' ?_ hcomp
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    have hq : epsilon * q = 1 := by
      dsimp [q]
      field_simp [ne_of_gt hepsilon]
    have hidentity : (s ^ epsilon) ^ q = s := by
      calc
        (s ^ epsilon) ^ q = s ^ (epsilon * q) := by
          rw [← Real.rpow_mul hs.le]
        _ = s := by rw [hq, Real.rpow_one]
    rw [Function.comp_apply, hidentity]
  have hexp : Tendsto
      (fun s : ℝ => Real.exp (-c * s ^ epsilon)) atTop (𝓝 0) := by
    have hcomp :=
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (0 : ℝ) c hc).comp hscale
    apply Tendsto.congr' ?_ hcomp
    filter_upwards [] with s
    simp only [Function.comp_apply, Real.rpow_zero, one_mul]
  have hlinear_exp_term : Tendsto
      (fun s : ℝ => (D * s + 1) * Real.exp (-c * s ^ epsilon)) atTop (𝓝 0) := by
    have hsum := ((tendsto_const_nhds (x := D)).mul hlinear_exp).add hexp
    simp only [mul_zero, zero_add] at hsum
    apply Tendsto.congr' ?_ hsum
    filter_upwards [] with s
    ring
  have hinv : Tendsto (fun s : ℝ => s ^ (-1 : ℝ)) atTop (𝓝 0) := by
    exact tendsto_rpow_neg_atTop (by norm_num)
  have hinv2 : Tendsto (fun s : ℝ => s ^ (-2 : ℝ)) atTop (𝓝 0) := by
    exact tendsto_rpow_neg_atTop (by norm_num)
  have hpoly : Tendsto
      (fun s : ℝ => (D * s + 1) * s ^ (-2 : ℝ)) atTop (𝓝 0) := by
    have hsum := ((tendsto_const_nhds (x := D)).mul hinv).add hinv2
    simp only [mul_zero, zero_add] at hsum
    apply Tendsto.congr' ?_ hsum
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    simp only [Real.rpow_neg hs.le, Real.rpow_two, Real.rpow_one]
    field_simp [ne_of_gt hs]
  let A : ℝ := (4 * kappa * C_p) ^ K
  have hpoly_term : Tendsto
      (fun s : ℝ => (D * s + 1) * (A * s ^ (-2 : ℝ))) atTop (𝓝 0) := by
    have hmul := (tendsto_const_nhds (x := A)).mul hpoly
    have hmul0 : Tendsto
        (fun s : ℝ => A * ((D * s + 1) * s ^ (-2 : ℝ))) atTop (𝓝 0) := by
      simpa only [mul_zero] using hmul
    apply Tendsto.congr' ?_ hmul0
    filter_upwards [] with s
    ring
  have hsum := hpoly_term.add hlinear_exp_term
  have hsum0 : Tendsto
      (fun s : ℝ => (D * s + 1) * (A * s ^ (-2 : ℝ)) +
        (D * s + 1) * Real.exp (-c * s ^ epsilon)) atTop (𝓝 0) := by
    simpa only [zero_add] using hsum
  apply Tendsto.congr' ?_ hsum0
  filter_upwards [] with s
  dsimp [A, epsilon]
  ring

end LPPDifferentiability

end
