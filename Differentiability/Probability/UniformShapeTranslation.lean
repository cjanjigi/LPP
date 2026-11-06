/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Probability.EnvironmentMap
public import LPP_Foundations.Model.LastPassage.Scaling
public import LPP_Foundations.Frozen.Model.Quadrant
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic

/-!
# Uniform shape laws under a constant change of weights

The exact finite passage shift identifies the full uniform shape event under the
product environment law of a translated marginal.
-/

public section

open MeasureTheory
open scoped NNReal

namespace LPPDifferentiability

/-- The all-endpoint uniform shape law is unchanged when every weight and the shape
are translated by the same linear level function. -/
theorem uniform_origin_shape_law_iff_map_add
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (g : Quadrant → ℝ) (c : ℝ) :
    (∀ᵐ ω ∂environmentLaw μ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage ω 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ)) ↔
    (∀ᵐ ω ∂environmentLaw (μ.map (fun x => x + c)), ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage ω 0 d -
          (g ((d.1 : ℝ≥0), (d.2 : ℝ≥0)) +
            c * ((d.1 : ℝ) + (d.2 : ℝ)))| ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ)) := by
  let shift : Environment → Environment := fun ω => ω + fun _ => c
  let shiftBack : Environment → Environment := fun ω => fun z => ω z - c
  let shiftEquiv : Environment ≃ᵐ Environment :=
    { toEquiv :=
        { toFun := shift
          invFun := shiftBack
          left_inv := by
            intro ω
            funext z
            dsimp [shift, shiftBack]
            ring
          right_inv := by
            intro ω
            funext z
            dsimp [shift, shiftBack]
            ring }
      measurable_toFun := by
        dsimp [shift]
        exact measurable_coordinatewise_environment_map
          (fun x : ℝ => x + c) (by fun_prop)
      measurable_invFun := by
        dsimp [shiftBack]
        exact measurable_coordinatewise_environment_map
          (fun x : ℝ => x - c) (by fun_prop) }
  have hshiftEmbedding : MeasurableEmbedding shift := shiftEquiv.measurableEmbedding
  have hshiftBackEmbedding : MeasurableEmbedding shiftBack :=
    shiftEquiv.symm.measurableEmbedding
  have hpush : (environmentLaw μ).map shift =
      environmentLaw (μ.map (fun x => x + c)) := by
    exact environmentLaw_map_coordinatewise μ (fun x : ℝ => x + c) (by fun_prop)
  have hcomp : shiftBack ∘ shift = id := by
    funext ω
    funext z
    change (ω z + c) - c = ω z
    ring
  have hpushBack :
      (environmentLaw (μ.map (fun x : ℝ => x + c))).map shiftBack =
        environmentLaw μ := by
    calc
      (environmentLaw (μ.map (fun x : ℝ => x + c))).map shiftBack =
          ((environmentLaw μ).map shift).map shiftBack := by rw [hpush]
      _ = (environmentLaw μ).map (shiftBack ∘ shift) :=
        Measure.map_map (shiftEquiv.symm.measurable) shiftEquiv.measurable
      _ = (environmentLaw μ).map id := by rw [hcomp]
      _ = environmentLaw μ := Measure.map_id
  let originalGood : Environment → Prop := fun ω =>
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 1 ≤ N ∧
      ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage ω 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ)
  let shiftedGood : Environment → Prop := fun ω =>
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 1 ≤ N ∧
      ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage ω 0 d -
          (g ((d.1 : ℝ≥0), (d.2 : ℝ≥0)) +
            c * ((d.1 : ℝ) + (d.2 : ℝ)))| ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ)
  have hcancel (ω : Environment) (d : ℕ × ℕ) :
      lastPassage (shift ω) 0 d -
          (g ((d.1 : ℝ≥0), (d.2 : ℝ≥0)) +
            c * ((d.1 : ℝ) + (d.2 : ℝ))) =
        lastPassage ω 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0)) := by
    dsimp [shift]
    rw [lastPassage_add_const]
    push_cast
    ring
  have hcancelBack (ω : Environment) (d : ℕ × ℕ) :
      lastPassage (shiftBack ω) 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0)) =
        lastPassage ω 0 d -
          (g ((d.1 : ℝ≥0), (d.2 : ℝ≥0)) +
            c * ((d.1 : ℝ) + (d.2 : ℝ))) := by
    have hshiftBackAsAdd : shiftBack ω = ω + fun _ : Lattice => -c := by
      funext z
      dsimp [shiftBack]
      ring
    rw [hshiftBackAsAdd, lastPassage_add_const]
    push_cast
    ring
  change (∀ᵐ ω ∂environmentLaw μ, originalGood ω) ↔
    ∀ᵐ ω ∂environmentLaw (μ.map (fun x => x + c)), shiftedGood ω
  constructor
  · intro hgood
    have hcomp : ∀ᵐ ω ∂environmentLaw μ, shiftedGood (shift ω) := by
      filter_upwards [hgood] with ω hω
      intro ε hε
      obtain ⟨N, hN, hbound⟩ := hω ε hε
      refine ⟨N, hN, ?_⟩
      intro d hd
      simpa only [hcancel] using hbound d hd
    rw [← hpush]
    exact hshiftEmbedding.ae_map_iff.mpr hcomp
  · intro hgood
    have hcomp : ∀ᵐ ω ∂environmentLaw (μ.map (fun x => x + c)),
        originalGood (shiftBack ω) := by
      filter_upwards [hgood] with ω hω
      intro ε hε
      obtain ⟨N, hN, hbound⟩ := hω ε hε
      refine ⟨N, hN, ?_⟩
      intro d hd
      simpa only [hcancelBack] using hbound d hd
    rw [← hpushBack]
    exact hshiftBackEmbedding.ae_map_iff.mpr hcomp

end LPPDifferentiability
