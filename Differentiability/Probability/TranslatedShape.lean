/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.WeakNegativeShape
public import LPP_Foundations.Probability.TranslationCylinder
public import LPP_Foundations.Model.LastPassage.Translate

/-!
# The weak-negative shape theorem at every lattice start

The event at the origin is pulled back by each translation of the environment.
Because the signed lattice is countable, one event works for all starts and all
positive real tolerances, and the original shape witness is kept.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace LPPDifferentiability

private theorem ae_all_starts_of_ae_origin
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (g : Quadrant → ℝ)
    (hg : ∀ᵐ ω ∂environmentLaw μ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage ω 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ)) :
    ∀ᵐ ω ∂environmentLaw μ, ∀ u : Lattice, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage ω u d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ) := by
  apply ae_all_iff.mpr
  intro u
  have htranslate := measurePreserving_environment_translation μ u
  have hpull := htranslate.quasiMeasurePreserving.ae hg
  filter_upwards [hpull] with ω hω
  intro ε hε
  obtain ⟨N, hN, hbound⟩ := hω ε hε
  refine ⟨N, hN, ?_⟩
  intro d hd
  simpa only [lastPassage_translate, add_zero] using hbound d hd

/-- Under the weak-negative shape hypotheses, the unique shape controls all signed
lattice starts on one event of the original environment. The threshold may
depend on the environment, the start, and the positive real tolerance. -/
theorem exists_unique_translated_shape_of_negative_moment_and_positive_tail
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : ∃ p : ℝ, 1 < p ∧
      (∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ p) ∂μ) < ∞)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞) :
    ∃! g : Quadrant → ℝ,
      Continuous g ∧
      (∀ (c : ℝ≥0) (x : Quadrant),
        g (c * x.1, c * x.2) = (c : ℝ) * g x) ∧
      (∀ (x y : Quadrant) (a b : ℝ≥0), a + b = 1 →
        (a : ℝ) * g x + (b : ℝ) * g y ≤
          g (a * x.1 + b * y.1, a * x.2 + b * y.2)) ∧
      (∀ᵐ ω ∂environmentLaw μ, ∀ u : Lattice, ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
          |lastPassage ω u d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
            ε * ((d.1 + d.2 : ℕ) : ℝ)) := by
  obtain ⟨g, hg, hunique⟩ :=
    exists_unique_shape_of_negative_moment_and_positive_tail μ hneg hpos
  refine ⟨g, ⟨hg.1, hg.2.1, hg.2.2.1,
    ae_all_starts_of_ae_origin μ g hg.2.2.2⟩, ?_⟩
  intro f hf
  apply hunique f
  refine ⟨hf.1, hf.2.1, hf.2.2.1, ?_⟩
  filter_upwards [hf.2.2.2] with ω hω
  exact hω 0

end LPPDifferentiability
