/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.TranslatedShape
public import Differentiability.Model.Paths.DefectAlgebra

import Mathlib.Tactic.Linarith

/-!
# Uniform lower bounds on path defects

The same translated shape error controls both extreme supporting defects,
uniformly over interior directions and paths.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace LPPDifferentiability

private theorem uniform_path_defect_on_shape_event
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (g : Quadrant → ℝ)
    (hgconc : ∀ (x y : Quadrant) (r s : ℝ≥0), r + s = 1 →
      (r : ℝ) * g x + (s : ℝ) * g y ≤ g (r • x + s • y))
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z)
    (hshape : ∀ᵐ ω ∂environmentLaw μ, ∀ u : Lattice, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage ω u d -
          g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ)) :
    ∀ᵐ ω ∂environmentLaw μ, ∀ u : Lattice, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ a : ℝ, 0 < a → a < 1 →
        ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 → ∀ p : Path u d,
          let H : ℝ → ℝ := fun h => quadrantExtension g (a + h, 1 - a - h)
          let dl := derivWithin H (Set.Iio 0) 0
          let dr := derivWithin H (Set.Ioi 0) 0
          let rho := (1 - a) * (d.1 : ℝ) - a * (d.2 : ℝ)
          let fminus := H 0 * ((d.1 : ℝ) + (d.2 : ℝ)) + dl * rho
          let fplus := H 0 * ((d.1 : ℝ) + (d.2 : ℝ)) + dr * rho
          fminus - pathWeight ω p ≥
              -ε * ((d.1 + d.2 : ℕ) : ℝ) ∧
            fplus - pathWeight ω p ≥
              -ε * ((d.1 + d.2 : ℕ) : ℝ) := by
  filter_upwards [hshape] with ω hω
  intro u ε hε
  obtain ⟨N, hN, hbound⟩ := hω u ε hε
  refine ⟨N, hN, ?_⟩
  intro a ha₀ ha₁ d hd p
  let z : Quadrant := ((d.1 : ℝ≥0), (d.2 : ℝ≥0))
  have hcanonical :=
    Path.canonical_path_defect_lower_bounds g hgconc hhom a ha₀ ha₁ ω p
  have hshapeLower :
      -ε * ((d.1 + d.2 : ℕ) : ℝ) ≤
        g z - lastPassage ω u d := by
    have herror := (abs_le.mp (hbound d hd)).2
    dsimp [z]
    linarith
  rcases hcanonical with ⟨hminus, hplus, hpassage⟩
  constructor
  · calc
      -ε * ((d.1 + d.2 : ℕ) : ℝ) ≤
          g z - lastPassage ω u d := hshapeLower
      _ ≤ g z - pathWeight ω p := hpassage
      _ ≤ _ := hminus
  · calc
      -ε * ((d.1 + d.2 : ℕ) : ℝ) ≤
          g z - lastPassage ω u d := hshapeLower
      _ ≤ g z - pathWeight ω p := hpassage
      _ ≤ _ := hplus

/-- The unique translated shape supplied by the negative-moment shape theorem
also gives one common threshold for both path defects, every interior direction,
and every directed path. The threshold depends
only on the sample, start, and positive tolerance. -/
theorem exists_unique_translated_shape_with_uniform_path_defect
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
          |lastPassage ω u d -
            g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
            ε * ((d.1 + d.2 : ℕ) : ℝ)) ∧
      (∀ᵐ ω ∂environmentLaw μ, ∀ u : Lattice, ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, 1 ≤ N ∧ ∀ a : ℝ, 0 < a → a < 1 →
          ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 → ∀ p : Path u d,
            let H : ℝ → ℝ := fun h => quadrantExtension g (a + h, 1 - a - h)
            let dl := derivWithin H (Set.Iio 0) 0
            let dr := derivWithin H (Set.Ioi 0) 0
            let rho := (1 - a) * (d.1 : ℝ) - a * (d.2 : ℝ)
            let fminus := H 0 * ((d.1 : ℝ) + (d.2 : ℝ)) + dl * rho
            let fplus := H 0 * ((d.1 : ℝ) + (d.2 : ℝ)) + dr * rho
            fminus - pathWeight ω p ≥
                -ε * ((d.1 + d.2 : ℕ) : ℝ) ∧
              fplus - pathWeight ω p ≥
                -ε * ((d.1 + d.2 : ℕ) : ℝ)) := by
  obtain ⟨g, hg, hunique⟩ :=
    exists_unique_translated_shape_of_negative_moment_and_positive_tail μ hneg hpos
  have hdefect :=
    uniform_path_defect_on_shape_event μ g hg.2.2.1 hg.2.1 hg.2.2.2
  refine ⟨g, ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2, hdefect⟩, ?_⟩
  intro f hf
  apply hunique f
  exact ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1⟩

end LPPDifferentiability

end
