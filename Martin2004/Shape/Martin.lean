/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Probability.MartinFirstMoment
public import Martin2004.Probability.MartinWeakContinuity
public import Martin2004.Probability.BoundedExpectedUniform
public import Martin2004.Probability.UniformTruncationApproximation
public import Martin2004.Probability.BoundedPassageFluctuations
public import Martin2004.Shape.ExpectedRateUniform
public import LPP_Foundations.Shape.Uniqueness

/-!
# The shape function under both square-root tails

This file proves the shape theorem of Martin (2004), Section 5.3 (Lemmas 5.2-5.5 together with
Theorem 2.3), in the form of `exists_unique_shape`: under both integrated square-root tails there
is exactly one continuous, homogeneous, concave function that is almost surely the uniform limit of
the scaled last-passage times. The same continuous expected rate gives every property. One
deterministic clipping level at each countable tolerance joins truncation, centered bounded
fluctuations, uniform means and relative rate approximation.

## Main results

- `LPPDifferentiability.Martin.exists_unique_shape`: existence and uniqueness of the shape
  function.

## References

- J. B. Martin, *Limiting shape for directed percolation models*, Ann. Probab. 32 (2004),
  Section 5.3 and Theorem 2.3.
-/

public section

open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

namespace LPPDifferentiability.Martin

private theorem scaled_superadditivity (g : Quadrant → ℝ)
    (hhom : ∀ (c : ℝ≥0) (x : Quadrant), g (c • x) = (c : ℝ) * g x)
    (hsuper : ∀ x y : Quadrant, g x + g y ≤ g (x + y))
    (x y : Quadrant) (a b : ℝ≥0) :
    (a : ℝ) * g x + (b : ℝ) * g y ≤
      g (a * x.1 + b * y.1, a * x.2 + b * y.2) := by
  have h := hsuper (a • x) (b • y)
  rw [hhom a x, hhom b y] at h
  exact h

/-- Martin's uniform shape theorem under both integrated square-root tails.
The same continuous actual expected rate supplies every property; any two continuous
homogeneous functions that are almost surely uniform limits of the scaled last-passage times are
equal. -/
theorem exists_unique_shape
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : (∫⁻ t in Iio (0 : ℝ), (μ (Iic t)) ^ (1 / 2 : ℝ)) < ∞)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞) :
    ∃! g : Quadrant → ℝ,
      Continuous g ∧
      (∀ (c : ℝ≥0) (x : Quadrant),
        g (c * x.1, c * x.2) = (c : ℝ) * g x) ∧
      (∀ (x y : Quadrant) (a b : ℝ≥0), a + b = 1 →
        (a : ℝ) * g x + (b : ℝ) * g y ≤
          g (a * x.1 + b * y.1, a * x.2 + b * y.2)) ∧
      (∀ᵐ ω ∂environmentLaw μ,
        ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ z : ℕ × ℕ,
          N ≤ z.1 + z.2 →
          |lastPassage ω (0, 0) z - g ((z.1 : ℝ≥0), (z.2 : ℝ≥0))| ≤
            ε * ((z.1 + z.2 : ℕ) : ℝ)) := by
  have hμ := integrable_id_of_martin_tails μ hneg hpos
  obtain ⟨g, hg, _hUniqueRate⟩ :=
    exists_unique_continuous_lastPassage_real_expected_rate_of_integrable_and_positive_tail
      μ hμ hpos
  have hhom := coordinate_homogeneity g hg.1.2.1
  have hae : ∀ᵐ ω ∂environmentLaw μ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ z : ℕ × ℕ, N ≤ z.1 + z.2 →
        |lastPassage ω (0, 0) z - g ((z.1 : ℝ≥0), (z.2 : ℝ≥0))| ≤
          ε * ((z.1 + z.2 : ℕ) : ℝ) := by
    apply ae_all_tolerances_of_reciprocals (environmentLaw μ)
      (fun ω z => |lastPassage ω (0, 0) z - g ((z.1 : ℝ≥0), (z.2 : ℝ≥0))|)
    intro j
    let τ : ℝ := 1 / ((j : ℝ) + 1)
    let δ : ℝ := τ / 8
    have hτ : 0 < τ := by dsimp only [τ]; positivity
    have hδ : 0 < δ := div_pos hτ (by norm_num)
    obtain ⟨L, hL, r, hr, ⟨Nm, _hNm, hm⟩, ht⟩ :=
      exists_common_clipping_approximation μ hneg hpos g hg.1.1.1 δ hδ
    have hc := ae_eventually_clipped_lastPassage_centered_uniform_deviation μ L hL
    filter_upwards [ht, hc] with ω hωt hωc
    obtain ⟨Nt, _hNt, htrunc⟩ := hωt
    obtain ⟨Nc, _hNc, hfluct⟩ := hωc δ hδ
    refine ⟨max 1 (max Nm (max Nt Nc)), ?_⟩
    intro z hz
    have hzm : Nm ≤ z.1 + z.2 :=
      (le_max_left Nm (max Nt Nc)).trans ((le_max_right 1 _).trans hz)
    have hzt : Nt ≤ z.1 + z.2 :=
      (le_max_left Nt Nc).trans ((le_max_right Nm _).trans ((le_max_right 1 _).trans hz))
    have hzc : Nc ≤ z.1 + z.2 :=
      (le_max_right Nt Nc).trans ((le_max_right Nm _).trans ((le_max_right 1 _).trans hz))
    have herr₄ := hr ((z.1 : ℝ≥0), (z.2 : ℝ≥0))
    simp only [NNReal.coe_natCast, ← Nat.cast_add] at herr₄
    rw [abs_sub_comm] at herr₄
    have hδτ : 4 * δ ≤ τ := by dsimp only [δ]; linarith only [hτ]
    exact four_errors_le _ _ _ _ _ δ τ _ (Nat.cast_nonneg _) hδτ
      (htrunc z hzt).le (hfluct z hzc).le (hm z hzm).le herr₄
  refine ⟨g, ⟨hg.2, hhom, ?_, hae⟩, ?_⟩
  · intro x y a b _hab
    exact scaled_superadditivity g hg.1.2.1 hg.1.2.2.1 x y a b
  · intro f hf
    exact shapeCandidates_eq μ f g hf.1 hg.2 hf.2.1 hhom hf.2.2.2 hae

end LPPDifferentiability.Martin
