/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.MartinRationalRate
public import Martin2004.Probability.MartinWeakNaturalRate

/-!
# Rational expected passage rates under a first moment

The positive square-root tail and an integrable marginal produce one unique
rational expected rate, with actual floor limits, denominator representation,
geometry, signed bounds and symmetry for the same witness. No extension to
real directions and no uniform rational limit is asserted. Existing exports
are unchanged.
-/

public section

open MeasureTheory Filter Set
open scoped Topology ENNReal NNRat

namespace LPPDifferentiability

/-- A first moment and the positive integrated square-root tail suffice for
one unique rational expected passage rate with the listed properties. The
natural-direction rate and every finite-passage integrability bound are built
inside the proof; no natural rate, geometric conclusion or negative tail is
assumed. -/
theorem exists_unique_lastPassage_rational_rate_of_integrable_and_positive_tail
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞) :
    ∃! F : (ℚ≥0 × ℚ≥0) → ℝ,
      (∀ q : ℚ≥0 × ℚ≥0, Tendsto (fun n : ℕ =>
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
        (environmentLaw μ)) := by
  classical
  obtain ⟨g, hg, _⟩ :=
    exists_unique_lastPassage_natural_shape_of_integrable_and_positive_tail μ hμ hpos
  have hswap := hg.2.2.2.2.2.2.2.2
  have hlim := fun a : ℕ × ℕ => (hg.1 a).1
  have hzero := hg.2.1
  have hscale : ∀ (k : ℕ) (a : ℕ × ℕ), g (k • a) = (k : ℝ) * g a :=
    fun k a => hg.2.2.1 a k
  have hadd := hg.2.2.2.1
  have hx := hg.2.2.2.2.1
  have hy := hg.2.2.2.2.2.1
  have hbounds := hg.2.2.2.2.2.2.1
  obtain ⟨F, hF, _⟩ := existsUnique_nnrat_rate_of_natural_homogeneous g hzero hscale
  have hFlim : ∀ q : ℚ≥0 × ℚ≥0, Tendsto (fun n : ℕ =>
      (∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (q.1 : ℝ)⌋₊, ⌊(n : ℝ) * (q.2 : ℝ)⌋₊)
        ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (F q)) := by
    intro q
    obtain ⟨d, hd, A, hA⟩ := nnrat_pair_exists_nat_div q
    have hmono : Monotone (fun z : ℕ × ℕ =>
        (∫ ω : Environment, lastPassage ω 0 z ∂environmentLaw μ) -
          ((z.1 + z.2 : ℕ) : ℝ) * (∫ x : ℝ, x ∂μ)) := by
      intro z w hzw
      exact integral_lastPassage_corrected_monotone μ hμ z w hzw.1 hzw.2
    have h := tendsto_rational_floor_of_corrected_ray
      (fun z => ∫ ω : Environment, lastPassage ω 0 z ∂environmentLaw μ)
      (∫ x : ℝ, x ∂μ) hmono A d hd (g A) (hlim A)
    rw [hA, hF d hd A]
    simpa only [Prod.fst, Prod.snd, NNRat.cast_div, NNRat.cast_natCast,
      ← mul_div_assoc] using h
  have haxes := nnrat_rate_axes g F hF (∫ x : ℝ, x ∂μ)
    (fun k => (hx k).trans (mul_comm _ _))
    (fun k => (hy k).trans (mul_comm _ _))
  refine ⟨F, ⟨hFlim, nnrat_rate_zero g hzero F hF,
    nnrat_rate_smul g hscale F hF, nnrat_rate_superadditive g hscale hadd F hF,
    haxes.1, haxes.2, nnrat_rate_swap g F hF hswap, ?_,
    ⟨g, hlim, hF⟩, ?_⟩, ?_⟩
  · intro q
    have hlo : ∀ a : ℕ × ℕ,
        (∫ x : ℝ, x ∂μ) * ((a.1 : ℝ) + a.2) ≤ g a := by
      intro a
      simpa only [Nat.cast_add, mul_comm] using (hbounds a).1
    have hup : ∀ a : ℕ × ℕ,
        g a ≤ (g (1, 1) - ∫ x : ℝ, x ∂μ) * ((a.1 : ℝ) + a.2) := by
      intro a
      simpa only [Nat.cast_add, mul_comm] using (hbounds a).2
    have hdiag : F (1, 1) = g (1, 1) := by
      exact nnrat_rate_natCast g F hF (1, 1)
    rw [hdiag]
    exact nnrat_rate_bounds g F hF (∫ x : ℝ, x ∂μ)
      (g (1, 1) - ∫ x : ℝ, x ∂μ) hlo hup q
  · intro z
    exact integrable_lastPassage μ hμ 0 z
  · intro H hH
    funext q
    exact tendsto_nhds_unique (hH.1 q) (hFlim q)

end LPPDifferentiability
