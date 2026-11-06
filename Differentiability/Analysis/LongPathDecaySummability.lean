/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Analysis.LongPathNumericDecay
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Positivity

/-! # Summability of the long-path scalar bound

The exact itinerary-count and allocation-count sequence is bounded
term by term by a constant multiple of the geometric sequence with ratio
`1 / 2`.
-/

public section

namespace LPPDifferentiability

/-- The scalar long-path sequence is summable under the numerical condition. -/
theorem long_path_decay_summable (q0 : ℝ) (hq0 : 0 < q0)
    (hsmall : 60 * (2 * q0) ^ (1 / 32 : ℝ) ≤ 1 / 2) :
    Summable (fun N : ℕ =>
      15 ^ N * 4 ^ N * (2 * q0) ^ ((N / 32 : ℕ) : ℝ)) := by
  apply Summable.of_nonneg_of_le (fun N => by positivity) ?_
    (summable_geometric_two.mul_left ((2 * q0) ^ (-1 : ℝ)))
  intro N
  rcases long_path_numeric_decay q0 hq0 hsmall N with ⟨hdecay, hgeometric⟩
  exact hdecay.trans hgeometric

end LPPDifferentiability
