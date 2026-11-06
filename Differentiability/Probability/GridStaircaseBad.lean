/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.SharpPathConcentration
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The bad-staircase bound for the grid lemma

A deterministic admissible path of length at most `8 c_* k² s` has weight below
`n E - t` with probability at most `exp (-t² / (16 c_* k² s M²))` when the weights
are bounded by `M`. This is (5.12) of the differentiability preprint, obtained from the
one-sided Hoeffding bound for a path.
-/

public section

open MeasureTheory ProbabilityTheory Real

namespace LPPDifferentiability

/-- **The bad-staircase bound (5.12) of the differentiability preprint.** For a path of
length `n ≤ 8 c_* k² s`, the probability that its weight is below `n E - t`, with `E` the
mean weight, is at most `exp (-t² / (16 c_* k² s M²))`. -/
theorem measure_staircase_bad_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {M t cstar s : ℝ} (k : ℕ)
    (hM : 0 < M) (ht : 0 < t) (hcstar : 0 < cstar) (hk : 1 ≤ k) (hs : 0 < s)
    (hb : ∀ᵐ x ∂μ, |x| ≤ M) {u : Lattice} {d : ℕ × ℕ} (p : Path u d)
    (hlen : ((d.1 + d.2 : ℕ) : ℝ) ≤ 8 * cstar * (k : ℝ) ^ 2 * s) :
    (environmentLaw μ).real {ω : Environment |
      pathWeight ω p < (d.1 + d.2 : ℕ) * ∫ x : ℝ, x ∂μ - t} ≤
        exp (-t ^ 2 / (16 * cstar * (k : ℝ) ^ 2 * s * M ^ 2)) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hB : 0 < 16 * cstar * (k : ℝ) ^ 2 * s * M ^ 2 := by positivity
  by_cases hn : d.1 + d.2 = 0
  · have hw : ∀ ω : Environment, pathWeight ω p = 0 := fun ω =>
      Finset.sum_eq_zero (fun i _ => absurd i.isLt (by omega))
    have hcast : ((d.1 + d.2 : ℕ) : ℝ) = 0 := by exact_mod_cast hn
    have hempty : {ω : Environment |
        pathWeight ω p < (d.1 + d.2 : ℕ) * ∫ x : ℝ, x ∂μ - t} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      rw [hw ω, hcast]
      linarith
    rw [hempty, measureReal_empty]
    exact (exp_pos _).le
  · have hnpos : (0 : ℝ) < ((d.1 + d.2 : ℕ) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hn
    refine (measure_pathWeight_lt_mean_sub_le μ hM ht hb p).trans ?_
    apply exp_le_exp.mpr
    have h1 : 2 * ((d.1 + d.2 : ℕ) : ℝ) * M ^ 2 ≤ 16 * cstar * (k : ℝ) ^ 2 * s * M ^ 2 := by
      nlinarith [sq_nonneg M]
    have h2 : t ^ 2 / (16 * cstar * (k : ℝ) ^ 2 * s * M ^ 2) ≤
        t ^ 2 / (2 * ((d.1 + d.2 : ℕ) : ℝ) * M ^ 2) :=
      div_le_div_of_nonneg_left (sq_nonneg t) (by positivity) h1
    rw [neg_div, neg_div]
    exact neg_le_neg h2

end LPPDifferentiability
