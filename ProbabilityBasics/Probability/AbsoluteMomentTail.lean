/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.PositiveMomentTail

/-!
# Absolute moments and one-sided tail inputs

A finite absolute moment above order two supplies the two one-sided
hypotheses used by the weak-negative shape theorem: a negative-part moment
above one and the positive integrated square-root tail.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace ProbabilityBasics

/-- A finite absolute moment of order greater than two gives the negative-part
moment and positive integrated square-root tail needed by the shape argument.
The moment comparison uses monotonicity of the real power; see Janjigian and
Rassoul-Agha, arXiv:1810.03580v3, assumption (2.1). -/
theorem negative_moment_and_positive_tail_of_absolute_moment
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {p : ℝ} (hp : 2 < p)
    (hmoment : (∫⁻ x, ENNReal.ofReal (|x| ^ p) ∂μ) < ∞) :
    (∃ q : ℝ, 1 < q ∧
      (∫⁻ x, ENNReal.ofReal ((max (-x) 0) ^ q) ∂μ) < ∞) ∧
    (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞ := by
  have hp0 : 0 < p := by linarith only [hp]
  have hpositiveMoment :
      (∫⁻ x, ENNReal.ofReal ((max x 0) ^ p) ∂μ) < ∞ := by
    apply lt_of_le_of_lt _ hmoment
    apply lintegral_mono
    intro x
    have hpart : 0 ≤ max x 0 := le_max_right x 0
    have habs : max x 0 ≤ |x| := max_le (le_abs_self x) (abs_nonneg x)
    exact ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow hpart habs hp0.le)
  have hpositiveTail :=
    LPPDifferentiability.positive_integrated_sqrt_tail_lt_top_of_moment
      μ hp hpositiveMoment
  have hnegativeMoment :
      (∫⁻ x, ENNReal.ofReal ((max (-x) 0) ^ p) ∂μ) < ∞ := by
    apply lt_of_le_of_lt _ hmoment
    apply lintegral_mono
    intro x
    have hpart : 0 ≤ max (-x) 0 := le_max_right (-x) 0
    have habs : max (-x) 0 ≤ |x| := max_le
      (by simpa only [abs_neg] using (le_abs_self (-x))) (abs_nonneg x)
    exact ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow hpart habs hp0.le)
  exact ⟨⟨p, by linarith only [hp], hnegativeMoment⟩, hpositiveTail⟩

end ProbabilityBasics
