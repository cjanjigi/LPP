/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# The scalar steps of the corner contradiction for unbounded weights

Two deterministic steps of the proof of Theorem 2.1 of the differentiability preprint for
unbounded weights, which uses Appendix B there. First, the linear defect of a path with `N ≥ 3`
full stages, fewer than `⌊N/32⌋` disjoint witnesses and total excess at most `N η s / 32`
(from (B.18)). Second, (B.15): since `p > 4`, `C₀ s^(2-p/4) ≤ η s / 64` for all large `s`.

## References

- C. Janjigian, F. Rassoul-Agha and T. Seppäläinen, *Differentiability of the shape function in
  the planar corner growth model*, preprint.
-/

public section

open Filter
open scoped Topology

namespace LPPDifferentiability

/-- From (B.18) of the differentiability preprint, `mult_tot < ⌊N/32⌋`, `N ≥ 3` and a
total excess `E ≤ N η s / 32`: `D ≥ (N-1) η s - 4 η s mult - E ≥ N (η s / 2)`, because
`(27/32) N - 1 ≥ N/2` for `N ≥ 3`. -/
theorem linear_defect_of_few_witnesses_excess (η s D E : ℝ) (N cap : ℕ) (hηs : 0 ≤ η * s)
    (hN : 3 ≤ N) (hcap : cap < N / 32) (hE : E ≤ (N : ℝ) * η * s / 32)
    (hD : ((N : ℝ) - 1) * η * s - 4 * η * s * (cap : ℝ) - E ≤ D) :
    (N : ℝ) * (η * s / 2) ≤ D := by
  have h32 : 32 * (cap + 1) ≤ N := by omega
  have hcapR : 32 * ((cap : ℝ) + 1) ≤ (N : ℝ) := by exact_mod_cast h32
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : 4 * η * s * (cap : ℝ) ≤ (η * s) * ((N : ℝ) / 8) := by
    have : 4 * (cap : ℝ) ≤ (N : ℝ) / 8 := by linarith
    nlinarith
  have h2 : (η * s) * 1 ≤ (η * s) * ((11 : ℝ) / 32 * (N : ℝ)) := by
    apply mul_le_mul_of_nonneg_left _ hηs
    linarith
  nlinarith

/-- The rare-excess bound (B.15) of the differentiability preprint: since `p > 4`, the exponent
`2 - p/4` is below `1`, so
`C₀ s^(2-p/4) ≤ η s / 64` for all large `s`. -/
theorem rare_excess_scale_eventually (C₀ η p : ℝ) (hp : 4 < p) (hη : 0 < η) :
    ∃ s₁ : ℝ, ∀ s : ℝ, s₁ ≤ s → C₀ * s ^ (2 - p / 4) ≤ η * s / 64 := by
  have hy : 0 < p / 4 - 1 := by linarith
  have hT : Tendsto (fun s : ℝ => C₀ * s ^ (-(p / 4 - 1))) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop hy).const_mul C₀
    rwa [mul_zero] at this
  have hev := hT.eventually (gt_mem_nhds (show (0 : ℝ) < η / 64 by positivity))
  obtain ⟨s₁, hs₁⟩ := eventually_atTop.mp (hev.and (eventually_gt_atTop (0 : ℝ)))
  refine ⟨s₁, fun s hs => ?_⟩
  obtain ⟨h1, h0⟩ := hs₁ s hs
  have hsplit : s ^ (2 - p / 4) = s * s ^ (-(p / 4 - 1)) := by
    rw [show 2 - p / 4 = 1 + -(p / 4 - 1) by ring, Real.rpow_add h0, Real.rpow_one]
  rw [hsplit]
  have := mul_le_mul_of_nonneg_left h1.le h0.le
  nlinarith

end LPPDifferentiability
