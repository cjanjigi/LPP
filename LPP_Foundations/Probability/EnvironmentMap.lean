/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Probability.CoordinateLaw

/-!
# Coordinatewise maps of the canonical environment

A measurable transformation applied at every site changes the canonical
environment law by applying the same transformation to its one-site marginal.
The coordinate marginals and independence also follow by composing the actual
independent coordinate evaluations with that transformation.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace LPPDifferentiability

/-- Applying a measurable real map at every site is a measurable environment map. -/
theorem measurable_coordinatewise_environment_map (φ : ℝ → ℝ) (hφ : Measurable φ) :
    Measurable (fun ω : Environment => fun z : Lattice => φ (ω z)) :=
  Measurable.of_eval fun z => hφ.comp (measurable_environment_eval z)

/-- The coordinate evaluations after a measurable map remain independent. -/
theorem iIndepFun_coordinatewise_environment_eval (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (φ : ℝ → ℝ) (hφ : Measurable φ) :
    iIndepFun (fun z (ω : Environment) => φ (ω z)) (environmentLaw μ) := by
  exact (iIndepFun_environment_eval μ).comp (fun _ : Lattice => φ) (fun _ => hφ)

/-- Each transformed coordinate has the pushforward of the original marginal law. -/
theorem environmentLaw_map_coordinatewise_eval (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (φ : ℝ → ℝ) (hφ : Measurable φ) (z : Lattice) :
    (environmentLaw μ).map (fun ω : Environment => φ (ω z)) = μ.map φ := by
  calc
    (environmentLaw μ).map (fun ω : Environment => φ (ω z)) =
        ((environmentLaw μ).map (fun ω : Environment => ω z)).map φ := by
      rw [Measure.map_map hφ (measurable_environment_eval z)]
      rfl
    _ = μ.map φ := by rw [environmentLaw_map_eval]

/-- The full transformed environment has the canonical product law with marginal `μ.map φ`. -/
theorem environmentLaw_map_coordinatewise (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (φ : ℝ → ℝ) (hφ : Measurable φ) :
    (environmentLaw μ).map (fun ω : Environment => fun z : Lattice => φ (ω z)) =
      environmentLaw (μ.map φ) := by
  change (Measure.infinitePi (fun _ : Lattice => μ)).map
      (fun ω : Environment => fun z : Lattice => φ (ω z)) =
    Measure.infinitePi (fun _ : Lattice => μ.map φ)
  exact Measure.infinitePi_map_pi (μ := fun _ : Lattice => μ)
    (f := fun _ => φ) (fun _ => hφ)

end LPPDifferentiability
