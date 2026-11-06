/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Analysis.ExponentialShapeFormula
public import LPP_Foundations.Analysis.ExponentialShapeVariational
public import Martin2004.Probability.ExponentialExitGrid
public import Martin2004.Probability.ExponentialLaw
public import Martin2004.Probability.MartinWeakContinuity
public import Martin2004.Shape.ExpectedRateShape
public import Martin2004.Shape.ExponentialShapeUpper

/-!
# The shape for exponential weights of mean 1

Martin (2004), in the proof of Theorem 2.4, states the formula `(√x₁ + √x₂)²` for Exp(1) weights,
attributing it to Rost (1981). The proof here goes through the stationary model instead of citing
the formula.

Let `g₀` be the expected-rate shape of `Exp(1)` given by the existence theorem, so `g₀`
is continuous with explicit values on the axes and at the origin. On the open quadrant `g₀` lies
below the exponential shape `γ` (stationary upper bound), and the exit-grid bound together with the
variational step and continuity of `g₀` gives the reverse inequality. On the axes and at the
origin the explicit values of `g₀` (the mean of `Exp(1)` is `1`) are those of `γ`. So `g₀ = γ`,
which is `isExpectedRateShape_expMeasure_one`. Uniqueness of limits then gives
`exponential_shape`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace LPPDifferentiability

/-- The formula quoted by Martin (2004) from Rost (1981), proved by the stationary model: for
i.i.d. Exp(1) weights, `E T(0, ⌊n x⌋)/n` tends to `(√x₁ + √x₂)²`. -/
theorem isExpectedRateShape_expMeasure_one :
    IsExpectedRateShape (expMeasure 1) exponentialShape := by
  obtain ⟨hmean, -, hpos⟩ := expMeasure_one_martin_hypotheses
  obtain ⟨g₀, hg₀, -⟩ :=
    exists_unique_continuous_lastPassage_real_expected_rate_of_integrable_and_positive_tail
      (expMeasure 1) hmean hpos
  obtain ⟨⟨⟨hrate, -, horigin, haxisH, haxisV, -, -⟩, -⟩, hcont⟩ := hg₀
  have hmean_one : ∫ t : ℝ, t ∂expMeasure 1 = 1 := by
    simpa using (integrable_and_integral_id_expMeasure one_pos).2
  have hle : ∀ z : Quadrant, g₀ z ≤ exponentialShape z :=
    le_exponentialShape_of_isExpectedRateShape hrate
  have heq : g₀ = exponentialShape := by
    funext z
    obtain ⟨s, t⟩ := z
    rcases eq_or_ne s 0 with rfl | hs
    · -- vertical axis and origin: explicit values from the existence theorem
      rcases eq_or_ne t 0 with rfl | ht
      · have h0 : g₀ (0, 0) = 0 := horigin
        simp [h0, exponentialShape]
      · rw [haxisV t, hmean_one]
        simp [exponentialShape]
    · rcases eq_or_ne t 0 with rfl | ht
      · -- horizontal axis
        rw [haxisH s, hmean_one]
        simp [exponentialShape]
      · -- open quadrant: the upper bound and the exit-grid lower bound
        have hs' : 0 < s := pos_iff_ne_zero.2 hs
        have ht' : 0 < t := pos_iff_ne_zero.2 ht
        refine le_antisymm (hle (s, t)) (exponentialShape_le_of_exitGridBound g₀ hs' ht' hle
          hcont.continuousAt ?_)
        intro K hK
        obtain ⟨hρ0, hρ1, hid⟩ := characteristicParameter_spec hs' ht'
        exact hid.symm.le.trans (stationaryRate_le_exitGridBound hrate hρ0 hρ1 hs' ht' hK)
  exact heq ▸ hrate

/-- For exponential weights of mean 1, any expected-rate shape `g` equals `(√x₁ + √x₂)²`. -/
theorem exponential_shape
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ = expMeasure 1)
    (g : Quadrant → ℝ)
    (hg : ∀ x : Quadrant, Tendsto (fun n : ℕ =>
        (∫ ω : Environment, lastPassage ω 0
          (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
          ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (g x)))
    (x : Quadrant) :
    g x = (Real.sqrt (x.1 : ℝ) + Real.sqrt (x.2 : ℝ)) ^ 2 := by
  subst hμ
  exact tendsto_nhds_unique (hg x) (isExpectedRateShape_expMeasure_one x)

end LPPDifferentiability
