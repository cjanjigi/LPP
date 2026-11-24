/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import LPP_Foundations.Frozen.Model.PathWeight
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-! # Trial bounds at characteristic record scales

Both versions of the grid estimate use the same short-crossing probability bound and
mesh inequality at each characteristic record scale (`lem:records` and `t.aux32`).
-/

@[expose] public section

open MeasureTheory Set

namespace LPPDifferentiability

/-- The crossing inequalities at record scales, from `lem:records` and `t.aux32`. -/
def gridRecordTrials (μ : Measure ℝ) [IsProbabilityMeasure μ] (a G K q0 : ℝ) (k0 : ℕ) (m : ℕ → ℕ)
    (record : Set ℕ) : Prop :=
  ∀ k ∈ record, 4 * k0 + 3 ≤ k → ∀ j : ℕ, j ≤ ⌈((m k : ℝ) - 1) / 4⌉₊ →
    (∀ n : ℕ, 1 ≤ n → (n : ℝ) < (2 : ℝ) ^ (m k - 4 * j - 1) →
      q0 < (environmentLaw μ).real {ω : Environment |
        ∃ u : Lattice, u.1 + u.2 = 0 ∧ ∃ e : ℕ × ℕ, e.1 + e.2 = n ∧ ∃ q : Path u e,
          (∀ i, |(1 - a) * ((q.vertex i).1 : ℝ) - a * ((q.vertex i).2 : ℝ)| ≤
            8 * (2 : ℝ) ^ (k - j)) ∧
          G * (n : ℝ) - K * (2 : ℝ) ^ (k - j) < pathWeight ω q}) ∧
    (1 < (2 : ℝ) ^ (m k - 4 * j - 1) →
      (2 : ℝ) ^ (m k - 4 * j - 1) ≤ ((2 : ℝ) ^ (k - j)) ^ 3 / 2)

end LPPDifferentiability
