/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Probability.CoordinateLaw
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding

import LPP_Foundations.Probability.Stationarity

/-!
# The measurable equivalence given by environment translation

Translating the lattice coordinates by `v` is an invertible measurable map of
the environment space. Its inverse is translation by `-v`. Both maps preserve
the canonical iid environment law.
-/

@[expose] public section

open MeasureTheory

namespace LPPDifferentiability

/-- The environment translation, with inverse translation by `-v`. -/
def environmentTranslationEquiv (v : Lattice) : Environment ≃ᵐ Environment where
  toEquiv :=
    { toFun := fun ω z => ω (v + z)
      invFun := fun ω z => ω (-v + z)
      left_inv := by
        intro ω
        funext z
        simp
      right_inv := by
        intro ω
        funext z
        simp }
  measurable_toFun := Measurable.of_eval fun z =>
    measurable_environment_eval (v + z)
  measurable_invFun := Measurable.of_eval fun z =>
    measurable_environment_eval (-v + z)

/-- Applying the environment translation reads the weight at `v + z`. -/
@[simp]
theorem environmentTranslationEquiv_apply (v : Lattice) (ω : Environment) (z : Lattice) :
    environmentTranslationEquiv v ω z = ω (v + z) := rfl

/-- Applying its inverse reads the weight at `-v + z`. -/
@[simp]
theorem environmentTranslationEquiv_symm_apply (v : Lattice) (ω : Environment)
    (z : Lattice) :
    (environmentTranslationEquiv v).symm ω z = ω (-v + z) := rfl

/-- The inverse followed by the translation is the identity. -/
@[simp]
theorem environmentTranslationEquiv_left_inv (v : Lattice) (ω : Environment) :
    (environmentTranslationEquiv v).symm (environmentTranslationEquiv v ω) = ω :=
  (environmentTranslationEquiv v).toEquiv.left_inv ω

/-- The translation followed by its inverse is the identity. -/
@[simp]
theorem environmentTranslationEquiv_right_inv (v : Lattice) (ω : Environment) :
    environmentTranslationEquiv v ((environmentTranslationEquiv v).symm ω) = ω :=
  (environmentTranslationEquiv v).toEquiv.right_inv ω

/-- Environment translation preserves the canonical iid law. -/
theorem measurePreserving_environmentTranslationEquiv (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (v : Lattice) :
    MeasurePreserving (environmentTranslationEquiv v) (environmentLaw μ) (environmentLaw μ) := by
  refine ⟨(environmentTranslationEquiv v).measurable, ?_⟩
  change (environmentLaw μ).map
      (fun ω : Environment => fun z : Lattice => ω (v + z)) = environmentLaw μ
  exact environmentLaw_map_translation μ v

/-- The inverse environment translation also preserves the canonical iid law. -/
theorem measurePreserving_environmentTranslationEquiv_symm (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (v : Lattice) :
    MeasurePreserving ((environmentTranslationEquiv v).symm)
      (environmentLaw μ) (environmentLaw μ) := by
  refine ⟨(environmentTranslationEquiv v).symm.measurable, ?_⟩
  change (environmentLaw μ).map
      (fun ω : Environment => fun z : Lattice => ω (-v + z)) = environmentLaw μ
  exact environmentLaw_map_translation μ (-v)

end LPPDifferentiability
