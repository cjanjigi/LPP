/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.Definitions.ProcessEnvironment
public import Busemann.Frozen.Definitions.ProcessShift
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Exact shift facts for the coupled process sample

These results record measurability, inverse shifts, and the environment
projection of the literal process shift.
-/

@[expose] public section

open MeasureTheory LPPDifferentiability

namespace LPP.Busemann

/-- The literal process shift is measurable, coordinate by coordinate; see
`Busemann/Frozen/Definitions/ProcessShift.lean:14-15`. -/
theorem measurable_processShift (z : Lattice) : Measurable (processShift z) := by
  change Measurable (fun s : ProcessSample =>
    (environmentTranslationEquiv z s.1, fun j x i => s.2 j (z + x) i))
  have hEnvironment : Measurable
      (fun s : ProcessSample => environmentTranslationEquiv z s.1) :=
    (environmentTranslationEquiv z).measurable.comp measurable_fst
  have hArray : Measurable
      (fun s : ProcessSample => fun j x i => s.2 j (z + x) i) := by
    apply measurable_pi_iff.mpr
    intro j
    apply measurable_pi_iff.mpr
    intro x
    apply measurable_pi_iff.mpr
    intro i
    exact (measurable_pi_apply i).comp
      ((measurable_pi_apply (z + x)).comp
        ((measurable_pi_apply j).comp measurable_snd))
  exact hEnvironment.prodMk hArray

/-- Shifting a sample by `z` and then by `-z` recovers it; see the literal
shift in `Busemann/Frozen/Definitions/ProcessShift.lean:14-15`. -/
theorem processShift_neg_processShift (z : Lattice) (s : ProcessSample) :
    processShift (-z) (processShift z s) = s := by
  apply Prod.ext
  · funext y
    simp [processShift, environmentTranslationEquiv_apply]
  · funext j x i
    simp [processShift]

/-- The environment component of the literal process shift is the canonical
translated environment; see `Busemann/Frozen/Definitions/ProcessShift.lean:14-15`
and `Busemann/Frozen/Definitions/ProcessEnvironment.lean:13`. -/
theorem processEnvironment_processShift (z : Lattice) (s : ProcessSample) :
    processEnvironment (processShift z s) =
      environmentTranslationEquiv z (processEnvironment s) := rfl

end LPP.Busemann
