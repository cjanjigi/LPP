/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import Martin2004.Model.ColumnPassage
public import Martin2004.Model.LastPassage.ShearComparison
public import LPP_Foundations.Probability.PassageIntegrable
public import LPP_Foundations.Probability.PassageMeasurable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.ProductMeasure

@[expose] public section

/-!
# The shear comparison for expectations (Martin 2004, equations (4.1)-(4.2))

In (4.1) and the display after it, Martin (2004) writes `E T(m, n)` as the mean of the same maximum
computed with sheared weights `X(ψ(z))`, because the shear `ψ(x, y) = (x + y, y)` is injective and
the weights are independent and identically distributed, and then bounds it by `E T̃(m + n, n)`.

This module has two results. `environmentLaw_map_shear` says that the sheared environment has the
same law: on the lattice `ℤ × ℤ` the shear is a bijection, so the reindexed independent family is
again the independent family with the same marginal.
`integral_lastPassage_le_integral_columnPassage` combines this with the path comparison of
`Model/LastPassage/ShearComparison.lean`.
-/

open MeasureTheory

namespace LPPDifferentiability

/-- Martin (2004), equation (4.1): the sheared environment `z ↦ ω (z.1 - z.2, z.2)` has the same
independent identically distributed law. On `ℤ × ℤ` the shear is a bijection, so the product measure
is carried to itself by reindexing the sites. -/
theorem environmentLaw_map_shear (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (environmentLaw μ).map (fun ω : Environment => fun z : Lattice => ω (z.1 - z.2, z.2)) =
      environmentLaw μ := by
  -- The shear `ψ(x, y) = (x + y, y)` as a bijection of the sites.
  let e : Lattice ≃ Lattice :=
    { toFun := fun z => (z.1 + z.2, z.2)
      invFun := fun z => (z.1 - z.2, z.2)
      left_inv := fun z => by simp
      right_inv := fun z => by simp }
  have hreindex := Measure.infinitePi_map_piCongrLeft (X := fun _ : Lattice => ℝ)
    (μ := fun _ : Lattice => μ) e
  -- Reindexing the coordinates along `e` is composing with the inverse shear.
  have hfun : ⇑(MeasurableEquiv.piCongrLeft (fun _ : Lattice => ℝ) e) =
      fun ω : Environment => fun z : Lattice => ω (z.1 - z.2, z.2) := by
    funext ω z
    obtain ⟨w, rfl⟩ := e.surjective z
    rw [MeasurableEquiv.piCongrLeft_apply_apply]
    simp [e]
  refine Eq.trans ?_ hreindex
  rw [hfun]
  rfl

/-- Martin (2004), the display after equation (4.1): for any weight law with a finite mean,
`E T(m, n) ≤ E T̃(m + n, n)`. The path weights of the sheared environment are bounded by
`T̃(m + n, n)` of that environment (`lastPassage_le_columnPassage_shear`), and the sheared
environment has the same law (`environmentLaw_map_shear`), so the expectation of `T̃(m + n, n)` is
unchanged by the shear. -/
theorem integral_lastPassage_le_integral_columnPassage (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ) (m n : ℕ) :
    ∫ ω, lastPassage ω 0 (m, n) ∂environmentLaw μ ≤
      ∫ ω, columnPassage ω (m + n) n ∂environmentLaw μ := by
  have hshear : Measurable (fun ω : Environment => fun z : Lattice => ω (z.1 - z.2, z.2)) :=
    Measurable.of_eval fun z => measurable_pi_apply _
  -- `T̃(m + n, n)` of the sheared environment is integrable, since the shear preserves the law.
  have hint_map : Integrable (fun ω : Environment => columnPassage ω (m + n) n)
      ((environmentLaw μ).map (fun ω : Environment => fun z : Lattice => ω (z.1 - z.2, z.2))) := by
    rw [environmentLaw_map_shear μ]
    exact integrable_columnPassage μ hμ (m + n) n
  have hint_sheared : Integrable
      (fun ω : Environment => columnPassage (fun z : Lattice => ω (z.1 - z.2, z.2)) (m + n) n)
      (environmentLaw μ) :=
    (integrable_map_measure hint_map.aestronglyMeasurable hshear.aemeasurable).mp hint_map
  -- The expectation of `T̃(m + n, n)` is the same for the sheared environment.
  have hvalue : ∫ ω, columnPassage (fun z : Lattice => ω (z.1 - z.2, z.2)) (m + n) n
        ∂environmentLaw μ = ∫ ω, columnPassage ω (m + n) n ∂environmentLaw μ := by
    have h := integral_map (μ := environmentLaw μ) hshear.aemeasurable
      (f := fun ω : Environment => columnPassage ω (m + n) n)
      (measurable_columnPassage (m + n) n).aestronglyMeasurable
    rw [environmentLaw_map_shear μ] at h
    exact h.symm
  rw [← hvalue]
  exact integral_mono (integrable_lastPassage μ hμ 0 (m, n)) hint_sheared
    (fun ω => lastPassage_le_columnPassage_shear ω m n)

end LPPDifferentiability
