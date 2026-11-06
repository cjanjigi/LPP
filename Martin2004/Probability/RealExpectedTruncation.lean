/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.MartinBoundedContinuity
public import Martin2004.Probability.MartinWeakRealExpectedRate
public import Martin2004.Probability.SelectedPathNegativeRemainder
public import Martin2004.Probability.ExpectedPositiveClipping
public import LPP_Foundations.Probability.TruncationTails

/-! # Expected rates of clipped laws

Whole environment law transport identifies the bounded-law expectations
with the literal clipped field on the original probability space. Finite
expected comparisons then pass through actual normalized floor limits.
-/

public section

open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

namespace LPPDifferentiability

/-- The literal clipped marginal is supported in its stated closed interval,
including cutoff zero and atoms at either endpoint. -/
theorem ae_abs_le_map_clipping (μ : Measure ℝ) (L : ℝ) (hL : 0 ≤ L) :
    ∀ᵐ x ∂μ.map (fun x : ℝ => max (-L) (min L x)), |x| ≤ L := by
  rw [ae_map_iff (by fun_prop : AEMeasurable (fun x : ℝ => max (-L) (min L x)) μ)
    (measurableSet_le (by fun_prop) measurable_const)]
  exact ae_of_all _ fun x => abs_le.mpr ⟨le_max_left _ _,
    max_le (by linarith only [hL]) (min_le_left _ _)⟩

/-- Whole product-law transport gives exactly the clipped finite passage mean.
No independence of a maximizing selected path is used in this identity. -/
theorem integral_lastPassage_map_clipping (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (L : ℝ) (d : ℕ × ℕ) :
    (∫ ω : Environment, lastPassage ω 0 d
      ∂environmentLaw (μ.map (fun x : ℝ => max (-L) (min L x)))) =
    ∫ ω : Environment, lastPassage (fun z => max (-L) (min L (ω z))) 0 d
      ∂environmentLaw μ := by
  have hm := measurable_coordinatewise_environment_map
    (fun x : ℝ => max (-L) (min L x)) (by fun_prop)
  rw [← environmentLaw_map_clipped]
  exact integral_map hm.aemeasurable (measurable_lastPassage 0 d).aestronglyMeasurable

/-- The unique bounded producer supplies an actual continuous clipped rate,
with all its expectation limits on both the mapped law and the original field. -/
theorem exists_continuous_clipped_real_expected_rate
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (L : ℝ) (hL : 0 ≤ L) :
    ∃ gL : Quadrant → ℝ, Continuous gL ∧
      (∀ x : Quadrant, Tendsto (fun n : ℕ =>
        (∫ ω : Environment, lastPassage ω 0
          (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
          ∂environmentLaw (μ.map (fun t : ℝ => max (-L) (min L t)))) / (n : ℝ))
        atTop (𝓝 (gL x))) ∧
      (∀ x : Quadrant, Tendsto (fun n : ℕ =>
        (∫ ω : Environment, lastPassage (fun z => max (-L) (min L (ω z))) 0
          (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
          ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (gL x))) := by
  obtain ⟨gL, hgL, _⟩ :=
    exists_unique_continuous_lastPassage_real_expected_rate_of_ae_abs_le
      (μ.map (fun x : ℝ => max (-L) (min L x))) L hL
      (ae_abs_le_map_clipping μ L hL)
  refine ⟨gL, hgL.2.1, hgL.1.1.1, ?_⟩
  intro x
  simpa only [integral_lastPassage_map_clipping] using hgL.1.1.1 x

/-- A finite comparison passes to actual floor expectation limits using the
actual normalized floor length. The error coefficient may be signed. -/
theorem real_expected_rate_sub_clipped_le_of_finite_comparison
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (L a : ℝ)
    (g gL : Quadrant → ℝ)
    (hg : ∀ x : Quadrant, Tendsto (fun n : ℕ =>
      (∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
        ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (g x)))
    (hgL : ∀ x : Quadrant, Tendsto (fun n : ℕ =>
      (∫ ω : Environment, lastPassage (fun z => max (-L) (min L (ω z))) 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
        ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (gL x)))
    (hfinite : ∀ d : ℕ × ℕ,
      (∫ ω : Environment, lastPassage ω 0 d ∂environmentLaw μ) -
        (∫ ω : Environment, lastPassage (fun z => max (-L) (min L (ω z))) 0 d
          ∂environmentLaw μ) ≤ ((d.1 + d.2 : ℕ) : ℝ) * a)
    (x : Quadrant) : g x - gL x ≤ ((x.1 : ℝ) + x.2) * a := by
  apply le_of_tendsto_of_tendsto' ((hg x).sub (hgL x))
    ((tendsto_floor_pair_length (x.1 : ℝ) (x.2 : ℝ)
      x.1.coe_nonneg x.2.coe_nonneg).mul_const a)
  intro n
  simpa only [sub_div, mul_div_right_comm] using
    div_le_div_of_nonneg_right
      (hfinite (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊))
      (Nat.cast_nonneg n : (0 : ℝ) ≤ n)

/-- The reverse finite comparison uses the same actual floor limits. -/
theorem clipped_sub_real_expected_rate_le_of_finite_comparison
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (L a : ℝ)
    (g gL : Quadrant → ℝ)
    (hg : ∀ x : Quadrant, Tendsto (fun n : ℕ =>
      (∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
        ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (g x)))
    (hgL : ∀ x : Quadrant, Tendsto (fun n : ℕ =>
      (∫ ω : Environment, lastPassage (fun z => max (-L) (min L (ω z))) 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
        ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (gL x)))
    (hfinite : ∀ d : ℕ × ℕ,
      (∫ ω : Environment, lastPassage (fun z => max (-L) (min L (ω z))) 0 d
          ∂environmentLaw μ) -
        (∫ ω : Environment, lastPassage ω 0 d ∂environmentLaw μ) ≤
          ((d.1 + d.2 : ℕ) : ℝ) * a)
    (x : Quadrant) : gL x - g x ≤ ((x.1 : ℝ) + x.2) * a := by
  apply le_of_tendsto_of_tendsto' ((hgL x).sub (hg x))
    ((tendsto_floor_pair_length (x.1 : ℝ) (x.2 : ℝ)
      x.1.coe_nonneg x.2.coe_nonneg).mul_const a)
  intro n
  simpa only [sub_div, mul_div_right_comm] using
    div_le_div_of_nonneg_right
      (hfinite (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊))
      (Nat.cast_nonneg n : (0 : ℝ) ≤ n)

/-- Martin's negative comparison for actual real expected rates uses the
literal first-moment residual; no negative square-root tail is required. -/
theorem clipped_real_expected_rate_sub_le_negative_remainder_mean
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ) (L : ℝ) (hL : 0 ≤ L)
    (g gL : Quadrant → ℝ)
    (hg : ∀ x : Quadrant, Tendsto (fun n : ℕ =>
      (∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
        ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (g x)))
    (hgL : ∀ x : Quadrant, Tendsto (fun n : ℕ =>
      (∫ ω : Environment, lastPassage (fun z => max (-L) (min L (ω z))) 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
        ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (gL x)))
    (x : Quadrant) :
    gL x - g x ≤ ((x.1 : ℝ) + x.2) * (∫ t : ℝ, max (-L - t) 0 ∂μ) := by
  apply clipped_sub_real_expected_rate_le_of_finite_comparison μ L _ g gL hg hgL
  intro d
  exact (integrable_and_integral_clipped_sub_lastPassage_le μ hμ L hL d).2.2.2

/-- The real positive tail vanishes by continuity of ENNReal.toReal at zero.
This conversion does not assume a negative tail condition. -/
theorem tendsto_martin_positive_tail_toReal_zero (μ : Measure ℝ)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞) :
    Tendsto (fun L : ℝ => (∫⁻ t in Ioi L,
      (μ (Ioi t)) ^ (1 / 2 : ℝ)).toReal) atTop (𝓝 0) := by
  simpa only [ENNReal.toReal_zero, Function.comp_def] using
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (tendsto_martin_positive_tail_zero μ hpos)

/-- One universal positive-tail constant controls the two actual real-rate
clipping comparisons. Both rates are tied to their actual floor expectations. -/
theorem exists_real_expected_rate_clipping_comparison :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
      Integrable (fun t : ℝ => t) μ →
      (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞ →
      ∀ g : Quadrant → ℝ,
      (∀ x : Quadrant, Tendsto (fun n : ℕ =>
        (∫ ω : Environment, lastPassage ω 0
          (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
          ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (g x))) →
      ∀ (L : ℝ), 0 ≤ L → ∃ gL : Quadrant → ℝ, Continuous gL ∧
      (∀ x : Quadrant, Tendsto (fun n : ℕ =>
        (∫ ω : Environment, lastPassage ω 0
          (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
          ∂environmentLaw (μ.map (fun t : ℝ => max (-L) (min L t)))) / (n : ℝ))
        atTop (𝓝 (gL x))) ∧
      (∀ x : Quadrant, Tendsto (fun n : ℕ =>
        (∫ ω : Environment, lastPassage (fun z => max (-L) (min L (ω z))) 0
          (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
          ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (gL x))) ∧
      (∀ x : Quadrant,
        gL x - ((x.1 : ℝ) + x.2) * (∫ t : ℝ, max (-L - t) 0 ∂μ) ≤ g x ∧
        g x ≤ gL x + C * ((x.1 : ℝ) + x.2) *
          (∫⁻ t in Ioi L, (μ (Ioi t)) ^ (1 / 2 : ℝ)).toReal) := by
  obtain ⟨C, hC, hpositive⟩ := exists_expected_positive_clipping_bound
  refine ⟨C, hC, ?_⟩
  intro μ _ hμ hpos g hg L hL
  obtain ⟨gL, hc, hmap, horig⟩ := exists_continuous_clipped_real_expected_rate μ L hL
  refine ⟨gL, hc, hmap, horig, ?_⟩
  intro x
  have hneg := clipped_real_expected_rate_sub_le_negative_remainder_mean
    μ hμ L hL g gL hg horig x
  have hpos' := real_expected_rate_sub_clipped_le_of_finite_comparison
    μ L (C * (∫⁻ t in Ioi L, (μ (Ioi t)) ^ (1 / 2 : ℝ)).toReal)
    g gL hg horig (fun d => by
      have h := (hpositive μ hμ hpos L hL d).2.2.2
      simpa only [mul_comm, mul_left_comm, mul_assoc] using h) x
  constructor
  · linarith only [hneg]
  · calc
      g x ≤ gL x + ((x.1 : ℝ) + x.2) *
          (C * (∫⁻ t in Ioi L, (μ (Ioi t)) ^ (1 / 2 : ℝ)).toReal) := by
            linarith only [hpos']
      _ = _ := by ring

end LPPDifferentiability
