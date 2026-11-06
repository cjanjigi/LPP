/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Heavy attachment parameter estimates

Integer and real-power arithmetic for the negative-moment exponent.
-/

public section

namespace LPPDifferentiability

/-- Every moment exponent above one admits an integer order `K` with `2 ≤ K` and
`K * (p - 1) ≥ 4`. -/
theorem exists_heavy_attachment_order (p : ℝ) (hp : 1 < p) :
    ∃ K : ℕ, 2 ≤ K ∧ (K : ℝ) * (p - 1) ≥ 4 := by
  let K : ℕ := 2 + Nat.ceil (4 / (p - 1))
  refine ⟨K, ?_, ?_⟩
  · dsimp [K]
    omega
  · have hp' : 0 < p - 1 := sub_pos.mpr hp
    have hceil : 4 / (p - 1) ≤ (Nat.ceil (4 / (p - 1)) : ℝ) :=
      Nat.le_ceil _
    have hprod : 4 ≤ (Nat.ceil (4 / (p - 1)) : ℝ) * (p - 1) :=
      (div_le_iff₀ hp').mp hceil
    dsimp [K]
    norm_num [Nat.cast_add]
    nlinarith

/-- The exponent `(p - 1) / (2 * p)` is positive. -/
theorem heavy_attachment_epsilon_pos (p : ℝ) (hp : 1 < p) :
    0 < (p - 1) / (2 * p) := by
  exact div_pos (sub_pos.mpr hp) (by positivity)

/-- The exponent `(p - 1) / (2 * p)` is less than one. -/
theorem heavy_attachment_epsilon_lt_one (p : ℝ) (hp : 1 < p) :
    (p - 1) / (2 * p) < 1 := by
  have hp0 : 0 < p := by linarith
  apply (div_lt_one (by positivity : 0 < 2 * p)).2
  nlinarith

/-- The moment `p` times the complementary exponent `1 - (p - 1) / (2 * p)` equals
`(p + 1) / 2`. -/
theorem heavy_attachment_complementary_exponent (p : ℝ) (hp : 1 < p) :
    p * (1 - (p - 1) / (2 * p)) = (p + 1) / 2 := by
  have hp0 : p ≠ 0 := ne_of_gt (by linarith)
  field_simp [hp0]
  ring

/-- The exponent `(p + 1) / 2` is strictly larger than one. -/
theorem heavy_attachment_complementary_exponent_gt_one
    (p : ℝ) (hp : 1 < p) :
    (p + 1) / 2 > 1 := by
  linarith

/-- The heavy-power identity, for a positive scale `s`. -/
theorem heavy_attachment_power_identity (p s : ℝ)
    (hp : 1 < p) (hs : 0 < s) :
    (s ^ (1 - (p - 1) / (2 * p))) ^ (-p) =
      s ^ (-(p + 1) / 2) := by
  have hp0 : p ≠ 0 := ne_of_gt (by linarith)
  have hexponent : (1 - (p - 1) / (2 * p)) * (-p) = -(p + 1) / 2 := by
    field_simp [hp0]
    ring
  rw [← Real.rpow_mul hs.le, hexponent]

end LPPDifferentiability

end
