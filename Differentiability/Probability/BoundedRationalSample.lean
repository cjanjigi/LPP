/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.MartinRationalRate

import Martin2004.Probability.BoundedMarginalTails
import LPP_Foundations.Model.LastPassage.LowerBoundMonotone

/-!
# Common rational sample limits for bounded marginal laws

The limits along natural rays and the rational expected rates are identified using
the actual limits of the expected passage times. A lower bound on every environment
weight gives monotonicity after subtracting that bound times the length of the path.
-/

public section

open MeasureTheory Filter Set
open scoped Topology ENNReal NNRat

namespace LPPDifferentiability

private theorem ae_rational_floor_limit_of_corrected_monotone
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (m : ℝ)
    (g : (ℕ × ℕ) → ℝ) (F : (ℚ≥0 × ℚ≥0) → ℝ)
    (hmono : ∀ᵐ ω ∂environmentLaw μ, Monotone (fun z : ℕ × ℕ =>
      lastPassage ω 0 z - ((z.1 + z.2 : ℕ) : ℝ) * m))
    (hcommon : ∀ᵐ ω ∂environmentLaw μ, ∀ a : ℕ × ℕ, Tendsto
      (fun n : ℕ => lastPassage ω 0 (n • a) / (n : ℝ)) atTop (𝓝 (g a)))
    (hrep : ∀ d : ℕ, 0 < d → ∀ a : ℕ × ℕ,
      F ((a.1 : ℚ≥0) / d, (a.2 : ℚ≥0) / d) = g a / (d : ℝ)) :
    ∀ᵐ ω ∂environmentLaw μ, ∀ q : ℚ≥0 × ℚ≥0, Tendsto
      (fun n : ℕ => lastPassage ω 0
        (⌊(n : ℝ) * (q.1 : ℝ)⌋₊, ⌊(n : ℝ) * (q.2 : ℝ)⌋₊) /
          (n : ℝ)) atTop (𝓝 (F q)) := by
  filter_upwards [hmono, hcommon] with ω hωmono hωcommon
  intro q
  obtain ⟨d, hd, A, hA⟩ := nnrat_pair_exists_nat_div q
  have h := tendsto_rational_floor_of_corrected_ray
    (fun z => lastPassage ω 0 z) m hωmono A d hd (g A) (hωcommon A)
  rw [hA, hrep d hd A]
  simpa only [Prod.fst, Prod.snd, NNRat.cast_div, NNRat.cast_natCast,
    ← mul_div_assoc] using h

/-- A bounded marginal law determines the same unique rational expected rate
with its full characterization and a common almost-sure rational sample limit. -/
theorem exists_unique_lastPassage_rational_shape_of_ae_abs_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (L : ℝ) (hL : 0 ≤ L)
    (hμ : ∀ᵐ x ∂μ, |x| ≤ L) :
    ∃! F : (ℚ≥0 × ℚ≥0) → ℝ,
      ((∀ q : ℚ≥0 × ℚ≥0, Tendsto (fun n : ℕ =>
        (∫ ω : Environment, lastPassage ω 0
          (⌊(n : ℝ) * (q.1 : ℝ)⌋₊, ⌊(n : ℝ) * (q.2 : ℝ)⌋₊)
          ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (F q))) ∧
      F 0 = 0 ∧
      (∀ (c : ℚ≥0) (q : ℚ≥0 × ℚ≥0), F (c • q) = (c : ℝ) * F q) ∧
      (∀ q r : ℚ≥0 × ℚ≥0, F q + F r ≤ F (q + r)) ∧
      (∀ q : ℚ≥0, F (q, 0) = (∫ x : ℝ, x ∂μ) * (q : ℝ)) ∧
      (∀ q : ℚ≥0, F (0, q) = (∫ x : ℝ, x ∂μ) * (q : ℝ)) ∧
      (∀ q : ℚ≥0 × ℚ≥0, F q.swap = F q) ∧
      (∀ q : ℚ≥0 × ℚ≥0,
        (∫ x : ℝ, x ∂μ) * ((q.1 : ℝ) + q.2) ≤ F q ∧
        F q ≤ (F (1, 1) - ∫ x : ℝ, x ∂μ) * ((q.1 : ℝ) + q.2)) ∧
      (∃ g : (ℕ × ℕ) → ℝ,
        (∀ a : ℕ × ℕ, Tendsto (fun n : ℕ =>
          (∫ ω : Environment, lastPassage ω 0 (n • a) ∂environmentLaw μ) /
            (n : ℝ)) atTop (𝓝 (g a))) ∧
        (∀ d : ℕ, 0 < d → ∀ a : ℕ × ℕ,
          F ((a.1 : ℚ≥0) / d, (a.2 : ℚ≥0) / d) = g a / (d : ℝ))) ∧
      (∀ z : ℕ × ℕ, Integrable (fun ω : Environment => lastPassage ω 0 z)
        (environmentLaw μ))) ∧
      (∀ᵐ ω ∂environmentLaw μ, ∀ q : ℚ≥0 × ℚ≥0, Tendsto
        (fun n : ℕ => lastPassage ω 0
          (⌊(n : ℝ) * (q.1 : ℝ)⌋₊, ⌊(n : ℝ) * (q.2 : ℝ)⌋₊) /
            (n : ℝ)) atTop (𝓝 (F q))) := by
  classical
  have hneg := lt_of_le_of_lt
    (integrated_negative_sqrt_tail_le_of_ae_abs_le μ L hL hμ)
    (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top : ENNReal.ofReal L < ∞)
  have hpos := lt_of_le_of_lt
    (integrated_positive_sqrt_tail_le_of_ae_abs_le μ L hL hμ)
    (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top : ENNReal.ofReal L < ∞)
  obtain ⟨F, hF, huniq⟩ :=
    exists_unique_lastPassage_rational_rate_of_martin_tails μ hneg hpos
  obtain ⟨g, hgmean, hrep⟩ := hF.2.2.2.2.2.2.2.2.1
  obtain ⟨G, hG, _⟩ :=
    exists_unique_lastPassage_natural_shape_of_martin_tails μ hneg hpos
  have hGg : G = g := by
    funext a
    exact tendsto_nhds_unique (hG.1 a).1 (hgmean a)
  have hcommon := hG.2.2.2.2.2.2.2
  rw [hGg] at hcommon
  have hlower : ∀ᵐ ω ∂environmentLaw μ, ∀ z : Lattice, -L ≤ ω z := by
    rw [ae_all_iff]
    intro z
    have hmap : ∀ᵐ x ∂(environmentLaw μ).map (fun ω : Environment => ω z),
        -L ≤ x := by
      rw [environmentLaw_map_eval]
      filter_upwards [hμ] with x hx
      exact (abs_le.mp hx).1
    exact ae_of_ae_map (measurable_environment_eval z).aemeasurable hmap
  have hmono : ∀ᵐ ω ∂environmentLaw μ, Monotone (fun z : ℕ × ℕ =>
      lastPassage ω 0 z - ((z.1 + z.2 : ℕ) : ℝ) * (-L)) := by
    filter_upwards [hlower] with ω hω
    exact lastPassage_corrected_monotone_of_lower_bound ω 0 (-L) hω
  refine ⟨F, ⟨hF, ?_⟩, ?_⟩
  · exact ae_rational_floor_limit_of_corrected_monotone μ (-L) g F
      hmono hcommon hrep
  · intro H hH
    exact huniq H hH.1

end LPPDifferentiability
