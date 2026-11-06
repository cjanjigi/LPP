/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Probability.CoordinateLaw

/-!
# Translation invariance of the environment law

Reindexing the independent identically distributed weights by an integer translation of the
lattice does not change their joint law.
-/

@[expose] public section

open MeasureTheory

namespace LPPDifferentiability

/-- Reindexing all weights by an integer translation preserves their joint law. -/
theorem environmentLaw_map_translation (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (v : Lattice) :
    (environmentLaw μ).map (fun ω : Environment => fun z => ω (v + z)) =
      environmentLaw μ := by
  have hinj : Function.Injective (fun z : Lattice => v + z) := by
    intro z w h
    exact add_left_cancel h
  exact Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : Lattice => μ) hinj

end LPPDifferentiability
