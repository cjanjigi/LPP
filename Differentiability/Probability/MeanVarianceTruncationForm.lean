/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.MeanVarianceTruncationTail

/-!
# Martin (2004), Lemma 4.3 with the square-root distance written as in Lemma 4.2

Lemma 4.3 of Martin (2004): let `F` satisfy the square-root tail conditions (2.6) and (2.7), and let
`ε > 0`. Then there is a distribution `F~` with bounded support, with the same mean and the same
variance as `F`, such that `∫ |F(s) - F~(s)|^(1/2) ds < ε` over the whole line.

The theorem `martin_truncation_mean_variance` (in `Probability/MeanVarianceTruncationTail`) proves
this content, with the integrand written as
`ENNReal.ofReal (|(μ (Iic s)).toReal - (ν (Iic s)).toReal| ^ (1/2))`. Here the integrand is written
as `(ENNReal.ofReal |μ.real (Iic s) - ν.real (Iic s)|) ^ (1/2)`, the form used in Lemma 4.2. The
two integrands are equal at every `s`, so the two integrals are equal. The theorem
`lintegral_sqrt_distance_eq_measureReal` states this equality, and `martin_lemma_4_3` restates the
result with the second form.

## References

* J. B. Martin, Limiting shape for directed percolation models, Ann. Probab. 32 (2004), Lemmas 4.2
  and 4.3.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LPPDifferentiability

/-- The two integrand forms of the square-root distance have the same whole-line integral. For each
`s`, `ENNReal.ofReal (|(μ (Iic s)).toReal - (ν (Iic s)).toReal| ^ (1/2))` equals
`(ENNReal.ofReal |μ.real (Iic s) - ν.real (Iic s)|) ^ (1/2)`: the measure of a set is its real
measure's `toReal` (`measureReal_def`), and the power of a nonnegative real under `ENNReal.ofReal`
can be moved inside (`ENNReal.ofReal_rpow_of_nonneg`). This is the conversion used in Lemma 4.2. -/
theorem lintegral_sqrt_distance_eq_measureReal (μ ν : Measure ℝ) :
    ∫⁻ s : ℝ, ENNReal.ofReal (|(μ (Iic s)).toReal - (ν (Iic s)).toReal| ^ (1 / 2 : ℝ)) =
      ∫⁻ s : ℝ, (ENNReal.ofReal |μ.real (Iic s) - ν.real (Iic s)|) ^ (1 / 2 : ℝ) := by
  refine lintegral_congr fun s => ?_
  rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num), measureReal_def,
    measureReal_def]

/-- **Martin (2004), Lemma 4.3.** Let `μ` be a probability measure satisfying the
square-root tail conditions (2.6) (`hpos`) and (2.7) (`hneg`), and let `ε > 0`. Then there is a
probability measure `ν` with bounded support, with the same mean and the same variance as `μ`, such
that the integral over the whole line of the square-root distance
`(ENNReal.ofReal |μ.real (Iic s) - ν.real (Iic s)|) ^ (1/2)` between the distribution functions of
`μ` and `ν` is less than `ENNReal.ofReal ε`. The proof is the truncation theorem
`martin_truncation_mean_variance`, which covers both tails, with the integrand converted by
`lintegral_sqrt_distance_eq_measureReal`. -/
theorem martin_lemma_4_3
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : (∫⁻ t in Iio (0 : ℝ), (μ (Iic t)) ^ (1 / 2 : ℝ)) < ∞)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ (∃ K : ℝ, ∀ᵐ t ∂ν, |t| ≤ K) ∧
      (∫ t : ℝ, t ∂ν) = ∫ t : ℝ, t ∂μ ∧
      (∫ t : ℝ, (t - ∫ s : ℝ, s ∂ν) ^ 2 ∂ν) = ∫ t : ℝ, (t - ∫ s : ℝ, s ∂μ) ^ 2 ∂μ ∧
      (∫⁻ s : ℝ, (ENNReal.ofReal |μ.real (Iic s) - ν.real (Iic s)|) ^ (1 / 2 : ℝ)) <
        ENNReal.ofReal ε := by
  obtain ⟨ν, hν, hbdd, hmean, hvar, hdist⟩ := martin_truncation_mean_variance μ hneg hpos ε hε
  refine ⟨ν, hν, hbdd, hmean, hvar, ?_⟩
  rw [← lintegral_sqrt_distance_eq_measureReal μ ν]
  exact hdist

end LPPDifferentiability

end
