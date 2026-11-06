/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Analysis.HeavyBadEventDecay
public import Differentiability.Analysis.HeavyAttachmentWeightSubstitution
import Mathlib.Tactic.Positivity

/-! # Total decay for the heavy attachment estimate

The three geometric failures and the path-weight failure use one common
integer order and give the scalar bound used in the heavy attachment estimate.
-/

public section

open Filter
open scoped Topology

namespace LPPDifferentiability

/-- The four failure terms, with one natural order and the ceiling length, tend to zero.
The function `F` below is local to this theorem. -/
theorem tendsto_heavy_attachment_total_failure
    (p C₁ Cₚ D eta kappa theta0 : ℝ) (K : ℕ)
    (hp : 1 < p) (hC₁ : 0 ≤ C₁) (hCₚ : 0 ≤ Cₚ) (hD : 1 ≤ D)
    (heta : 0 < eta) (hkappa : 0 < kappa) (htheta0 : 0 < theta0)
    (hK : 2 ≤ K) (hKp : 4 ≤ (K : ℝ) * (p - 1)) :
    let L : ℕ := 4 * K + 4
    let B : ℝ := 8 * D / (theta0 * kappa) + 2
    let C : ℝ := Cₚ * (64 * (K : ℝ) / eta) ^ p
    let epsilon : ℝ := (p - 1) / (2 * p)
    let m : ℝ → ℕ := fun s => Nat.ceil (kappa * s)
    let F : ℝ → ℝ := fun s =>
      (48 * D * s ^ 2 * (C * s ^ (-p)) ^ 2 +
        (D * s + 1 + B * ((L + 1 : ℕ) : ℝ) ^ 2) * (C * s ^ (-p)) +
        (D * s + 1) *
          (((((2 * K + 5) * (m s + 1) : ℕ) : ℝ) *
            (C * s ^ (-p))) ^ K)) +
      (D * s + 1) *
        ((2 * (m s : ℝ) * Cₚ * (s ^ (1 - epsilon)) ^ (-p)) ^ K +
          Real.exp (-((eta * s / 16) ^ 2) /
            (2 * s ^ (1 - epsilon) *
              (2 * C₁ * (m s : ℝ) + (eta * s / 16) / 3))))
    Tendsto F atTop (𝓝 0) ∧ ∀ s, 0 < s → 0 ≤ F s := by
  dsimp only
  have hB : 0 ≤ 8 * D / (theta0 * kappa) + 2 := by positivity
  have hC : 0 ≤ Cₚ * (64 * (K : ℝ) / eta) ^ p := by positivity
  have hbad := tendsto_heavy_bad_event_bound_sum
    p kappa D (8 * D / (theta0 * kappa) + 2)
    (Cₚ * (64 * (K : ℝ) / eta) ^ p) K (4 * K + 4)
    hp hK hKp hkappa hD hB hC
  have hweight := tendsto_heavy_attachment_weight_failure
    p C₁ Cₚ D eta kappa K hp hC₁ hCₚ hD heta hkappa hK hKp
  constructor
  · simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, zero_add] using
      hbad.add hweight
  · intro s hs
    have hD0 : 0 ≤ D := le_trans (by norm_num) hD
    positivity

end LPPDifferentiability

end
