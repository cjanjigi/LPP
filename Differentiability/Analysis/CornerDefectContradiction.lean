/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# The scalar steps of the corner contradiction

Two deterministic steps of the proof of Theorem 2.1 of the differentiability preprint. First,
(6.17) there: a path with `N ≥ 3` full stages and fewer than `⌊N/32⌋` disjoint witnesses has
defect at least `N η s / 2`. Second, the contradiction: if for every `n` there is a stage count
`N` with `n ≤ 2 m (N + 1)` whose defect is at least `c N` once `N` is large, and the defect is
`o(n)`, then `c ≤ 0`.

## References

- C. Janjigian, F. Rassoul-Agha and T. Seppäläinen, *Differentiability of the shape function in
  the planar corner growth model*, preprint.
-/

public section

open Filter
open scoped Topology

namespace LPPDifferentiability

/-- The linear defect bound (6.17) of the differentiability preprint. From (6.16) there,
`mult_tot < ⌊N/32⌋` and `N ≥ 3`: `D ≥ (N-1) η s - 4 η s mult - excess` and `excess ≤ 0`
give `D ≥ N (η s / 2)`. -/
theorem linear_defect_of_few_witnesses (η s D E : ℝ) (N cap : ℕ) (hηs : 0 ≤ η * s)
    (hN : 3 ≤ N) (hcap : cap < N / 32) (hE : E ≤ 0)
    (hD : ((N : ℝ) - 1) * η * s - 4 * η * s * (cap : ℝ) - E ≤ D) :
    (N : ℝ) * (η * s / 2) ≤ D := by
  have h32 : 32 * (cap + 1) ≤ N := by omega
  have hcapR : 32 * ((cap : ℝ) + 1) ≤ (N : ℝ) := by exact_mod_cast h32
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : 4 * η * s * (cap : ℝ) ≤ (η * s) * ((N : ℝ) / 8) := by
    have : 4 * (cap : ℝ) ≤ (N : ℝ) / 8 := by linarith
    nlinarith
  have h2 : (η * s) * 1 ≤ (η * s) * ((3 : ℝ) / 8 * (N : ℝ)) := by
    apply mul_le_mul_of_nonneg_left _ hηs
    linarith
  nlinarith

/-- The contradiction at the end of the proof of Theorem 2.1 of the differentiability preprint.
If for every `n`
some `N` has `n ≤ 2 m (N+1)` and, once `N0 ≤ N`, defect at least `c N`, while the
defect is `o(n)`, then `c ≤ 0`. -/
theorem corner_defect_contradiction (D : ℕ → ℝ) (m N0 : ℕ) (hm : 1 ≤ m) (c : ℝ)
    (hc : 0 < c)
    (hstages : ∀ n : ℕ, ∃ N : ℕ, n ≤ 2 * m * (N + 1) ∧ (N0 ≤ N → c * (N : ℝ) ≤ D n))
    (hsub : Tendsto (fun n : ℕ => D n / (n : ℝ)) atTop (𝓝 0)) : False := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hε : 0 < c / (4 * m) := by positivity
  obtain ⟨N1, hN1⟩ := Metric.tendsto_atTop.1 hsub (c / (4 * m)) hε
  let n : ℕ := max (max N1 (4 * m)) (2 * m * (N0 + 1) + 1)
  have hn1 : N1 ≤ n := (le_max_left _ _).trans (le_max_left _ _)
  have hn2 : 4 * m ≤ n := (le_max_right _ _).trans (le_max_left _ _)
  have hn3 : 2 * m * (N0 + 1) + 1 ≤ n := le_max_right _ _
  obtain ⟨N, hnN, hD⟩ := hstages n
  have hNN0 : N0 ≤ N := by
    by_contra h
    have : 2 * m * (N + 1) ≤ 2 * m * (N0 + 1) := Nat.mul_le_mul_left _ (by omega)
    omega
  have hDn := hD hNN0
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnN' : (n : ℝ) ≤ 2 * m * ((N : ℝ) + 1) := by exact_mod_cast hnN
  have hn4 : 4 * (m : ℝ) ≤ n := by exact_mod_cast hn2
  have hlow : c / (4 * m) ≤ D n / n := by
    rw [div_le_div_iff₀ (by positivity) hnpos]
    -- c n ≤ 4 m D n, using D n ≥ c N and 2 m (N+1) ≥ n ≥ 4 m
    have hN2 : (n : ℝ) / (2 * m) - 1 ≤ N := by
      rw [sub_le_iff_le_add, div_le_iff₀ (by positivity)]
      linarith
    have hNge : (n : ℝ) / 4 / m ≤ N := by
      have : (n : ℝ) / 4 / m ≤ (n : ℝ) / (2 * m) - 1 := by
        rw [div_div, div_sub_one (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      linarith
    have hNge' : (n : ℝ) ≤ 4 * m * N := by
      rw [div_div, div_le_iff₀ (by positivity)] at hNge
      linarith
    nlinarith
  have hup := hN1 n hn1
  rw [Real.dist_eq, sub_zero] at hup
  have := (le_abs_self _).trans_lt hup
  linarith

end LPPDifferentiability
