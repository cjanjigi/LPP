/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Analysis.HeavyAttachmentDecay
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Substitution in the heavy attachment weight bound

The actual ceiling length and the source's choices of truncation and deviation
produce its literal polynomial and exponential failure estimate.
-/

public section

open Filter
open scoped Topology

namespace LPPDifferentiability

/-- The exact source exponential rate is positive. -/
theorem heavy_attachment_weight_rate_pos (C₁ eta kappa : ℝ)
    (hC₁ : 0 ≤ C₁) (heta : 0 < eta) (hkappa : 0 < kappa) :
    0 < eta ^ 2 / (512 * (4 * C₁ * kappa + eta / 48)) := by
  positivity

/-- Substituting the source parameters in the finite-path weight failure bound
is eventually dominated by the exact source polynomial-exponential term. -/
theorem eventually_heavy_attachment_weight_failure_le
    (p C₁ C_p D eta kappa : ℝ) (K : ℕ)
    (hp : 1 < p) (hC₁ : 0 ≤ C₁) (hC_p : 0 ≤ C_p) (hD : 1 ≤ D)
    (heta : 0 < eta) (hkappa : 0 < kappa) (_hKtwo : 2 ≤ K)
    (hK : 4 ≤ (K : ℝ) * (p - 1)) :
    ∀ᶠ s : ℝ in atTop,
      (D * s + 1) *
          ((2 * (Nat.ceil (kappa * s) : ℝ) * C_p *
                (s ^ (1 - (p - 1) / (2 * p))) ^ (-p)) ^ K +
            Real.exp (-((eta * s / 16) ^ 2) /
              (2 * s ^ (1 - (p - 1) / (2 * p)) *
                (2 * C₁ * (Nat.ceil (kappa * s) : ℝ) + eta * s / 16 / 3)))) ≤
        (D * s + 1) *
          ((4 * kappa * C_p) ^ K * s ^ (-2 : ℝ) +
            Real.exp (-(eta ^ 2 / (512 * (4 * C₁ * kappa + eta / 48))) *
              s ^ ((p - 1) / (2 * p)))) := by
  filter_upwards [eventually_ge_atTop (max 1 (1 / kappa))] with s hs
  have hs1 : 1 ≤ s := (le_max_left _ _).trans hs
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs1
  have hks : 1 ≤ kappa * s := by
    have hdiv : 1 / kappa ≤ s := (le_max_right _ _).trans hs
    have hmul := (div_le_iff₀ hkappa).mp hdiv
    linarith only [hmul]
  have hm : (Nat.ceil (kappa * s) : ℝ) ≤ 2 * kappa * s := by
    have hceil := (Nat.ceil_lt_add_one (mul_nonneg hkappa.le hs0.le)).le
    linarith only [hceil, hks]
  have hpower : s * s ^ (-(p + 1) / 2) = s ^ ((1 - p) / 2) := by
    calc
      s * s ^ (-(p + 1) / 2) = s ^ (1 : ℝ) * s ^ (-(p + 1) / 2) := by
        rw [Real.rpow_one]
      _ = s ^ (1 + -(p + 1) / 2) := (Real.rpow_add hs0 _ _).symm
      _ = s ^ ((1 - p) / 2) := by congr 1; ring
  have hheavy_base :
      2 * (Nat.ceil (kappa * s) : ℝ) * C_p *
          (s ^ (1 - (p - 1) / (2 * p))) ^ (-p) ≤
        (4 * kappa * C_p) * s ^ ((1 - p) / 2) := by
    rw [heavy_attachment_power_identity p s hp hs0]
    calc
      2 * (Nat.ceil (kappa * s) : ℝ) * C_p * s ^ (-(p + 1) / 2) ≤
          2 * (2 * kappa * s) * C_p * s ^ (-(p + 1) / 2) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hm (by norm_num)) hC_p)
          (Real.rpow_nonneg hs0.le _)
      _ = (4 * kappa * C_p) * (s * s ^ (-(p + 1) / 2)) := by ring
      _ = (4 * kappa * C_p) * s ^ ((1 - p) / 2) := by rw [hpower]
  have hheavy :
      (2 * (Nat.ceil (kappa * s) : ℝ) * C_p *
          (s ^ (1 - (p - 1) / (2 * p))) ^ (-p)) ^ K ≤
        (4 * kappa * C_p) ^ K * s ^ (-2 : ℝ) :=
    (pow_le_pow_left₀ (by positivity) hheavy_base K).trans
      (heavy_attachment_power_bound p kappa C_p s K hK hkappa hC_p hs1)
  let epsilon : ℝ := (p - 1) / (2 * p)
  let b : ℝ := s ^ (1 - epsilon)
  let A : ℝ := 4 * C₁ * kappa + eta / 48
  have hb : 0 < b := Real.rpow_pos_of_pos hs0 _
  have hA : 0 < A := by dsimp [A]; positivity
  have hbracket :
      2 * C₁ * (Nat.ceil (kappa * s) : ℝ) + eta * s / 16 / 3 ≤ A * s := by
    have hmul := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ 2 * C₁)
    dsimp [A]
    nlinarith only [hmul]
  have hden : 0 < 2 * b *
      (2 * C₁ * (Nat.ceil (kappa * s) : ℝ) + eta * s / 16 / 3) := by
    positivity
  have hden_le :
      2 * b * (2 * C₁ * (Nat.ceil (kappa * s) : ℝ) + eta * s / 16 / 3) ≤
        2 * b * (A * s) :=
    mul_le_mul_of_nonneg_left hbracket (by positivity)
  have hpower_cancel : s ^ epsilon * b = s := by
    dsimp [b]
    rw [← Real.rpow_add hs0]
    rw [show epsilon + (1 - epsilon) = 1 by ring, Real.rpow_one]
  have hscale : s / b = s ^ epsilon :=
    (div_eq_iff (ne_of_gt hb)).mpr hpower_cancel.symm
  have hratio_identity :
      (eta * s / 16) ^ 2 / (2 * b * (A * s)) =
        (eta ^ 2 / (512 * A)) * s ^ epsilon := by
    calc
      (eta * s / 16) ^ 2 / (2 * b * (A * s)) =
          (eta ^ 2 / (512 * A)) * (s / b) := by
        field_simp [ne_of_gt hs0, ne_of_gt hb, ne_of_gt hA]
        ring
      _ = (eta ^ 2 / (512 * A)) * s ^ epsilon := by rw [hscale]
  have hratio : (eta ^ 2 / (512 * A)) * s ^ epsilon ≤
      (eta * s / 16) ^ 2 /
        (2 * b * (2 * C₁ * (Nat.ceil (kappa * s) : ℝ) + eta * s / 16 / 3)) := by
    rw [← hratio_identity]
    exact div_le_div_of_nonneg_left (sq_nonneg _) hden hden_le
  have hexp :
      Real.exp (-((eta * s / 16) ^ 2) /
          (2 * b * (2 * C₁ * (Nat.ceil (kappa * s) : ℝ) + eta * s / 16 / 3))) ≤
        Real.exp (-(eta ^ 2 / (512 * A)) * s ^ epsilon) := by
    apply Real.exp_le_exp.mpr
    simpa only [neg_div, neg_mul] using neg_le_neg hratio
  have hD0 : 0 ≤ D := le_trans (by norm_num) hD
  exact mul_le_mul_of_nonneg_left (add_le_add hheavy hexp) (by positivity)

/-- The literal failure expression at the actual ceiling length tends to zero. -/
theorem tendsto_heavy_attachment_weight_failure
    (p C₁ C_p D eta kappa : ℝ) (K : ℕ)
    (hp : 1 < p) (hC₁ : 0 ≤ C₁) (hC_p : 0 ≤ C_p) (hD : 1 ≤ D)
    (heta : 0 < eta) (hkappa : 0 < kappa) (hKtwo : 2 ≤ K)
    (hK : 4 ≤ (K : ℝ) * (p - 1)) :
    Tendsto
      (fun s : ℝ => (D * s + 1) *
        ((2 * (Nat.ceil (kappa * s) : ℝ) * C_p *
              (s ^ (1 - (p - 1) / (2 * p))) ^ (-p)) ^ K +
          Real.exp (-((eta * s / 16) ^ 2) /
            (2 * s ^ (1 - (p - 1) / (2 * p)) *
              (2 * C₁ * (Nat.ceil (kappa * s) : ℝ) + eta * s / 16 / 3)))))
      atTop (𝓝 0) := by
  apply squeeze_zero' ?_
    (eventually_heavy_attachment_weight_failure_le
      p C₁ C_p D eta kappa K hp hC₁ hC_p hD heta hkappa hKtwo hK)
    (tendsto_heavy_attachment_failure_term p kappa C_p
      (eta ^ 2 / (512 * (4 * C₁ * kappa + eta / 48))) D K hp
      (heavy_attachment_weight_rate_pos C₁ eta kappa hC₁ heta hkappa))
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
  have hD0 : 0 ≤ D := le_trans (by norm_num) hD
  positivity

end LPPDifferentiability

end
