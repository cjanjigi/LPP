/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Probability.CoordinateLaw
public import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-!
# Exchanging the two lattice coordinates

Swapping the two coordinates of each lattice site is a measure-preserving map of the canonical
environment, so the i.i.d. environment law is unchanged by the swap.
-/

@[expose] public section

open MeasureTheory

namespace LPPDifferentiability

/-- Exchange the two lattice coordinates in an environment. -/
def environmentSwap (ω : Environment) : Environment := fun z => ω z.swap

@[simp]
theorem environmentSwap_apply (ω : Environment) (z : Lattice) :
    environmentSwap ω z = ω z.swap := rfl

/-- Swapping the coordinates twice returns the original environment. -/
theorem environmentSwap_involutive (ω : Environment) :
    environmentSwap (environmentSwap ω) = ω := by
  funext z
  simp [environmentSwap]

/-- The coordinate swap is measurable on the full environment space. -/
theorem measurable_environmentSwap : Measurable environmentSwap :=
  Measurable.of_eval fun z => measurable_environment_eval z.swap

/-- The full iid environment law is unchanged by exchanging lattice coordinates. -/
theorem environmentLaw_map_environmentSwap (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (environmentLaw μ).map environmentSwap = environmentLaw μ := by
  change (Measure.infinitePi (fun _ : Lattice => μ)).map
      (fun ω : Environment => fun z : Lattice => ω z.swap) =
    Measure.infinitePi (fun _ : Lattice => μ)
  have hinj : Function.Injective (fun z : Lattice => z.swap) := by
    intro z w h
    simpa using congrArg Prod.swap h
  exact Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : Lattice => μ) hinj

/-- Coordinate exchange preserves the iid environment law. -/
theorem measurePreserving_environmentSwap (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    MeasurePreserving environmentSwap (environmentLaw μ) (environmentLaw μ) := by
  exact ⟨measurable_environmentSwap, environmentLaw_map_environmentSwap μ⟩

end LPPDifferentiability
