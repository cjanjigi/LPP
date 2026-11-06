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

/-! # Scalar decay estimates for heavy vertices

The two limits used in the heavy-vertices argument. These
estimates concern the exact scalar sequences; they do not assert probability
bounds or independence of events.
-/

public section

open Filter
open scoped Topology

namespace LPPDifferentiability

/-- The polynomial factor in the global heavy-vertex union bound is dominated
by the exponential decay when `p > 4`. -/
theorem heavy_vertex_global_tail_decay {p epsilon C : ℝ}
    (hp : 4 < p) (hepsilon : 0 < epsilon) (hC : 0 ≤ C) :
    Tendsto (fun k : ℕ =>
      C * ((2 : ℝ) ^ k) ^ 4 * (((k : ℝ) / epsilon) ^ p) * ((2 : ℝ) ^ k) ^ (-p))
      atTop (𝓝 0) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hexp : 0 < (p - 4) * Real.log 2 := mul_pos (by linarith) hlog
  have hreal : Tendsto (fun x : ℝ => x ^ p * Real.exp (-((p - 4) * Real.log 2) * x))
      atTop (𝓝 0) := by
    exact tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p ((p - 4) * Real.log 2) hexp
  have hnat := hreal.comp tendsto_natCast_atTop_atTop
  have hscaled : Tendsto (fun k : ℕ =>
      (|C| * epsilon ^ (-p)) *
        ((k : ℝ) ^ p * Real.exp (-((p - 4) * Real.log 2) * (k : ℝ)))) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero] using hnat.const_mul (|C| * epsilon ^ (-p))
  have hCabs : C = |C| := (abs_of_nonneg hC).symm
  have hEq : (fun k : ℕ =>
      C * ((2 : ℝ) ^ k) ^ 4 * (((k : ℝ) / epsilon) ^ p) * ((2 : ℝ) ^ k) ^ (-p)) =ᶠ[atTop]
      (fun k : ℕ =>
        (|C| * epsilon ^ (-p)) *
          ((k : ℝ) ^ p * Real.exp (-((p - 4) * Real.log 2) * (k : ℝ)))) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
    have hkpos : 0 < (k : ℝ) := by exact_mod_cast hk
    have hspos : 0 < (2 : ℝ) ^ k := pow_pos zero_lt_two _
    have hfour : ((2 : ℝ) ^ k) ^ 4 = ((2 : ℝ) ^ k) ^ (4 : ℝ) :=
      (Real.rpow_natCast ((2 : ℝ) ^ k) 4).symm
    have hsub : ((2 : ℝ) ^ k) ^ 4 / ((2 : ℝ) ^ k) ^ p =
        ((2 : ℝ) ^ k) ^ (4 - p) := by
      rw [hfour]
      exact (Real.rpow_sub hspos 4 p).symm
    have hpower : ((2 : ℝ) ^ k) ^ (4 - p) =
        Real.exp (-((p - 4) * Real.log 2) * (k : ℝ)) := by
      rw [← Real.rpow_natCast (2 : ℝ) k,
        ← Real.rpow_mul (le_of_lt zero_lt_two) (k : ℝ) (4 - p),
        Real.rpow_def_of_pos zero_lt_two]
      congr 1
      ring
    calc
      C * ((2 : ℝ) ^ k) ^ 4 * (((k : ℝ) / epsilon) ^ p) * ((2 : ℝ) ^ k) ^ (-p)
          = C * ((2 : ℝ) ^ k) ^ 4 * ((k : ℝ) ^ p / epsilon ^ p) *
              ((2 : ℝ) ^ k) ^ (-p) := by
                rw [Real.div_rpow hkpos.le hepsilon.le]
      _ = C * ((2 : ℝ) ^ k) ^ 4 * ((k : ℝ) ^ p * epsilon ^ (-p)) *
              (((2 : ℝ) ^ k) ^ p)⁻¹ := by
                rw [div_eq_mul_inv, ← Real.rpow_neg hepsilon.le p,
                  Real.rpow_neg hspos.le p]
      _ = (C * epsilon ^ (-p)) *
              ((k : ℝ) ^ p * (((2 : ℝ) ^ k) ^ 4 / ((2 : ℝ) ^ k) ^ p)) := by
                rw [div_eq_mul_inv]
                ring
      _ = (C * epsilon ^ (-p)) *
              ((k : ℝ) ^ p * ((2 : ℝ) ^ k) ^ (4 - p)) := by
                exact congrArg (fun z : ℝ => (C * epsilon ^ (-p)) * ((k : ℝ) ^ p * z)) hsub
      _ = (C * epsilon ^ (-p)) *
              ((k : ℝ) ^ p * Real.exp (-((p - 4) * Real.log 2) * (k : ℝ))) := by
                exact congrArg (fun z : ℝ => (C * epsilon ^ (-p)) * ((k : ℝ) ^ p * z)) hpower
      _ = (|C| * epsilon ^ (-p)) *
              ((k : ℝ) ^ p * Real.exp (-((p - 4) * Real.log 2) * (k : ℝ))) := by
                exact congrArg (fun c : ℝ => c * epsilon ^ (-p) *
                  ((k : ℝ) ^ p * Real.exp (-((p - 4) * Real.log 2) * (k : ℝ)))) hCabs
  exact hscaled.congr' hEq.symm

/-- The coarse-block heavy-vertex tail tends to zero and is eventually at most
half of any fixed positive trial probability. -/
theorem heavy_vertex_block_tail_decay {p Cp q0 : ℝ}
    (hp : 4 < p) (hCp : 0 ≤ Cp) (hq0 : 0 < q0) :
    Tendsto (fun k : ℕ =>
      17 * Cp * (2 : ℝ) ^ (-(p - 4) * ((k : ℝ) - 3) / 4)) atTop (𝓝 0) ∧
    (∀ᶠ k : ℕ in atTop,
      17 * Cp * (2 : ℝ) ^ (-(p - 4) * ((k : ℝ) - 3) / 4) ≤ q0 / 2) := by
  let alpha : ℝ := (p - 4) / 4
  have halpha : 0 < alpha := by
    dsimp [alpha]
    linarith
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbase : 0 < (2 : ℝ) ^ (-alpha) := Real.rpow_pos_of_pos zero_lt_two _
  have hbase_lt : (2 : ℝ) ^ (-alpha) < 1 := by
    rw [Real.rpow_def_of_pos zero_lt_two]
    exact Real.exp_lt_one_iff.mpr
      (mul_neg_of_pos_of_neg hlog (by linarith))
  have hgeom : Tendsto (fun k : ℕ => ((2 : ℝ) ^ (-alpha)) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hbase.le hbase_lt
  have hscaled : Tendsto (fun k : ℕ =>
      (17 * |Cp| * (2 : ℝ) ^ (3 * alpha)) * ((2 : ℝ) ^ (-alpha)) ^ k)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using hgeom.const_mul (17 * |Cp| * (2 : ℝ) ^ (3 * alpha))
  have hpow (k : ℕ) :
      (2 : ℝ) ^ (-(p - 4) * ((k : ℝ) - 3) / 4) =
        (2 : ℝ) ^ (3 * alpha) * ((2 : ℝ) ^ (-alpha)) ^ k := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (-alpha)) k,
      ← Real.rpow_mul (le_of_lt zero_lt_two) (-alpha) (k : ℝ),
      ← Real.rpow_add zero_lt_two (3 * alpha) ((-alpha) * (k : ℝ))]
    congr 1
    dsimp [alpha]
    ring
  have hCpabs : Cp = |Cp| := (abs_of_nonneg hCp).symm
  have hEq : (fun k : ℕ =>
      17 * Cp * (2 : ℝ) ^ (-(p - 4) * ((k : ℝ) - 3) / 4)) =ᶠ[atTop]
      (fun k : ℕ => (17 * |Cp| * (2 : ℝ) ^ (3 * alpha)) *
        ((2 : ℝ) ^ (-alpha)) ^ k) := by
    filter_upwards with k
    calc
      17 * Cp * (2 : ℝ) ^ (-(p - 4) * ((k : ℝ) - 3) / 4) =
          17 * Cp * ((2 : ℝ) ^ (3 * alpha) * ((2 : ℝ) ^ (-alpha)) ^ k) := by
            rw [hpow k]
      _ = 17 * |Cp| * ((2 : ℝ) ^ (3 * alpha) * ((2 : ℝ) ^ (-alpha)) ^ k) := by
            exact congrArg (fun c : ℝ => 17 * c *
              ((2 : ℝ) ^ (3 * alpha) * ((2 : ℝ) ^ (-alpha)) ^ k)) hCpabs
      _ = (17 * |Cp| * (2 : ℝ) ^ (3 * alpha)) * ((2 : ℝ) ^ (-alpha)) ^ k := by ring
  have hlimit := hscaled.congr' hEq.symm
  refine ⟨hlimit, ?_⟩
  have hhalf : 0 < q0 / 2 := by linarith
  have hevent : ∀ᶠ k : ℕ in atTop,
      17 * Cp * (2 : ℝ) ^ (-(p - 4) * ((k : ℝ) - 3) / 4) < q0 / 2 :=
    hlimit.eventually (Iio_mem_nhds hhalf)
  exact hevent.mono fun _ hk => hk.le

end LPPDifferentiability
