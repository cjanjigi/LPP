/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LPP_Foundations.Frozen.Model.Quadrant
public import LPP_Foundations.Model.LastPassage.Translate
public import LPP_Foundations.Probability.TranslationEquiv
import Mathlib.Tactic

/-! Transfer a uniform origin shape estimate to every fixed lattice start. -/

public section

open MeasureTheory LPPDifferentiability
open scoped ENNReal NNReal Topology

namespace LPP

/-- An almost sure uniform shape estimate at the origin holds simultaneously from
every fixed lattice start by translation invariance and countability. This is the
translation step in Georgiou–Rassoul-Agha–Seppäläinen,
arXiv:1510.00860v2, Theorem 4.3; its origin estimate is an explicit input. -/
theorem ae_uniform_passage_shape_all_starts_of_origin
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (g : Quadrant → ℝ)
    (hOrigin : ∀ᵐ ω ∂environmentLaw μ,
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ z : ℕ × ℕ,
        N ≤ z.1 + z.2 →
        |lastPassage ω (0, 0) z - g ((z.1 : ℝ≥0), (z.2 : ℝ≥0))| ≤
          ε * ((z.1 + z.2 : ℕ) : ℝ)) :
    ∀ᵐ ω ∂environmentLaw μ, ∀ x : Lattice,
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ z : ℕ × ℕ,
        N ≤ z.1 + z.2 →
        |lastPassage ω x z - g ((z.1 : ℝ≥0), (z.2 : ℝ≥0))| ≤
          ε * ((z.1 + z.2 : ℕ) : ℝ) := by
  -- Pull the origin event back through the actual translation of the iid law.
  have hAtStart : ∀ x : Lattice, ∀ᵐ ω ∂environmentLaw μ,
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ z : ℕ × ℕ,
        N ≤ z.1 + z.2 →
        |lastPassage ω x z - g ((z.1 : ℝ≥0), (z.2 : ℝ≥0))| ≤
          ε * ((z.1 + z.2 : ℕ) : ℝ) := by
    intro x
    have htranslateLaw := measurePreserving_environmentTranslationEquiv μ x
    filter_upwards [htranslateLaw.quasiMeasurePreserving.ae hOrigin] with ω hω
    intro ε hε
    obtain ⟨N, hN⟩ := hω ε hε
    refine ⟨N, ?_⟩
    intro z hz
    have htranslate :
        lastPassage (environmentTranslationEquiv x ω) (0, 0) z =
          lastPassage ω x z := by
      change lastPassage (fun y : Lattice => ω (x + y)) 0 z = lastPassage ω x z
      simpa only [add_zero] using lastPassage_translate ω x 0 z
    simpa only [htranslate] using hN z hz

  -- A countable intersection gives one event for all fixed signed starts.
  exact ae_all_iff.mpr hAtStart

end LPP

end
