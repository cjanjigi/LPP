/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Optimizing the column bound over the parameter `ρ`

This file contains the real-variable optimization used in the proof of Martin (2004), Lemma 4.1,
in "Limiting shape for directed percolation models". It covers the calculation that follows the
bound (4.2) there.

The input is a real number `E` (an expected value) and nonnegative numbers `m`, `N`, and `p` in
`[0, 1]`. The hypotheses are:

* `E ≤ m`, the trivial bound (the parameter choice `ρ = 1`);
* `E ≤ m * ρ + N * (p * (1 - ρ) / (ρ - p))` for every `ρ` strictly between `p` and `1`.

The conclusion is `E ≤ m * p + 2 * √(m * N * (p * (1 - p)))`.

Proof idea. Write `q = 1 - p`, `K = m * N * (p * q)`, and `t = √K`. Substitute `s = ρ - p`, so the
second hypothesis becomes `E ≤ m * p + m * s + N * p * q / s - N * p`. If the best `s` is below
`q`, take `s = t / m`; AM-GM gives the value `m * s + N * p * q / s = 2 * t` at that point. If it is
not, the trivial bound `E ≤ m` already gives the claim.
-/

public section

namespace LPPDifferentiability

/-- The calculation after the bound (4.2) in the proof of Martin (2004), Lemma 4.1.
If `E ≤ m`, and `E ≤ m * ρ + N * (p * (1 - ρ) / (ρ - p))` for every `ρ` strictly between
`p` and `1`, then `E ≤ m * p + 2 * √(m * N * (p * (1 - p)))`. The inputs are `m, N ≥ 0` and
`p ∈ [0, 1]`. -/
theorem le_mul_add_two_sqrt_of_stationary_bounds {E m N p : ℝ} (hm : 0 ≤ m) (hN : 0 ≤ N)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (htriv : E ≤ m)
    (hstat : ∀ ρ : ℝ, p < ρ → ρ < 1 → E ≤ m * ρ + N * (p * (1 - ρ) / (ρ - p))) :
    E ≤ m * p + 2 * Real.sqrt (m * N * (p * (1 - p))) := by
  have hq : 0 ≤ 1 - p := by linarith
  have hNp0 : 0 ≤ N * p := mul_nonneg hN hp0
  have hK : 0 ≤ m * N * (p * (1 - p)) := mul_nonneg (mul_nonneg hm hN) (mul_nonneg hp0 hq)
  set K : ℝ := m * N * (p * (1 - p)) with hKdef
  set t : ℝ := Real.sqrt K
  have ht0 : 0 ≤ t := Real.sqrt_nonneg K
  have htt : t * t = K := Real.mul_self_sqrt hK
  -- The bound for one value `s = ρ - p` in `(0, 1 - p)`, before any optimization.
  have key : ∀ s : ℝ, 0 < s → s < 1 - p →
      E ≤ m * p + m * s + (N * (p * (1 - p)) / s - N * p) := by
    intro s hs0 hs1
    have hsne : s ≠ 0 := ne_of_gt hs0
    have hρ := hstat (p + s) (by linarith) (by linarith)
    have h1 : p + s - p = s := by ring
    have h2 : N * (p * (1 - (p + s)) / (p + s - p)) = N * (p * (1 - p)) / s - N * p := by
      rw [h1]
      field_simp
      ring
    have hm' : m * (p + s) = m * p + m * s := by ring
    rw [h2] at hρ
    linarith
  by_cases hcase : m * (1 - p) ≤ 2 * t
  · -- Case A: the trivial bound `E ≤ m` is enough, since `m = m * p + m * (1 - p)`.
    have hm1 : m = m * p + m * (1 - p) := by ring
    linarith
  · replace hcase := not_le.mp hcase
    have hmq : 0 < m * (1 - p) := by linarith
    have hm_pos : 0 < m := by
      rcases eq_or_lt_of_le hm with h | h
      · rw [← h, zero_mul] at hmq
        exact (lt_irrefl _ hmq).elim
      · exact h
    have hq_pos : 0 < 1 - p := by
      rcases eq_or_lt_of_le hq with h | h
      · rw [← h, mul_zero] at hmq
        exact (lt_irrefl _ hmq).elim
      · exact h
    rcases eq_or_lt_of_le ht0 with ht_zero | ht_pos
    · -- Case B1: `t = 0`, so `K = 0`, which forces `N * p = 0` (since `m > 0` and `1 - p > 0`).
      have hK0 : K = 0 := by
        rw [← htt, ← ht_zero, mul_zero]
      have hprod : m * (1 - p) * (N * p) = 0 := by
        have e : m * (1 - p) * (N * p) = K := by
          rw [hKdef]
          ring
        exact e.trans hK0
      have hNp : N * p = 0 :=
        (mul_eq_zero.mp hprod).resolve_left (mul_pos hm_pos hq_pos).ne'
      have hz0 : N * (p * (1 - p)) = 0 := by
        rw [← mul_assoc, hNp, zero_mul]
      -- With `N * p = 0` the bound is `E ≤ m * p + m * s` for every `s` in `(0, 1 - p)`.
      have hbound : ∀ s : ℝ, 0 < s → s < 1 - p → E ≤ m * p + m * s := by
        intro s hs0 hs1
        have h := key s hs0 hs1
        rw [hz0, zero_div, hNp] at h
        linarith
      -- Choose `s` small enough to get `E ≤ m * p`.
      have hEp : E ≤ m * p := by
        by_contra hne
        replace hne := not_le.mp hne
        have hd : 0 < E - m * p := by linarith
        set s : ℝ := min ((1 - p) / 2) ((E - m * p) / (2 * m)) with hsdef
        have hs0 : 0 < s := by
          rw [hsdef]
          exact lt_min (by linarith) (div_pos hd (by linarith))
        have hs1 : s < 1 - p := by
          have : s ≤ (1 - p) / 2 := min_le_left _ _
          linarith
        have hsm : s ≤ (E - m * p) / (2 * m) := min_le_right _ _
        have hmne : m ≠ 0 := hm_pos.ne'
        have hms : m * s ≤ (E - m * p) / 2 := by
          calc m * s ≤ m * ((E - m * p) / (2 * m)) := mul_le_mul_of_nonneg_left hsm hm
            _ = (E - m * p) / 2 := by
              field_simp
        have h := hbound s hs0 hs1
        linarith
      linarith
    · -- Case B2: `t > 0`. Take `s = t / m`, which lies in `(0, 1 - p)` because `t < m * (1 - p)`.
      have hmne : m ≠ 0 := hm_pos.ne'
      have hs0 : 0 < t / m := div_pos ht_pos hm_pos
      have hs1 : t / m < 1 - p := by
        rw [div_lt_iff₀ hm_pos, mul_comm]
        linarith
      have h := key (t / m) hs0 hs1
      have hms : m * (t / m) = t := by
        field_simp
      have hz : N * (p * (1 - p)) / (t / m) = t := by
        rw [div_div_eq_mul_div, div_eq_iff ht_pos.ne', htt, hKdef]
        ring
      rw [hz] at h
      linarith

end LPPDifferentiability
