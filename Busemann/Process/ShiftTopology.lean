/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Process.Shifts
public import Mathlib.Topology.Constructions

/-!
# Topology and group laws for the literal process shift

The process shift is continuous and obeys the additive translation law of the
underlying lattice.
-/

@[expose] public section

open LPPDifferentiability

namespace LPP.Busemann

/-- The literal process shift is continuous; see
`Busemann/Frozen/Definitions/ProcessShift.lean:14-15`. -/
theorem continuous_processShift (z : Lattice) : Continuous (processShift z) := by
  change Continuous (fun s : ProcessSample =>
    (environmentTranslationEquiv z s.1, fun j x i => s.2 j (z + x) i))
  have hEnvironment : Continuous
      (fun s : ProcessSample => environmentTranslationEquiv z s.1) := by
    apply continuous_pi
    intro y
    simpa only [Function.comp_def, environmentTranslationEquiv_apply] using
      (continuous_apply (z + y)).comp continuous_fst
  have hArray : Continuous
      (fun s : ProcessSample => fun j x i => s.2 j (z + x) i) := by
    apply continuous_pi
    intro j
    apply continuous_pi
    intro x
    apply continuous_pi
    intro i
    exact (continuous_apply i).comp
      ((continuous_apply (z + x)).comp
        ((continuous_apply j).comp continuous_snd))
  exact hEnvironment.prodMk hArray

/-- Shifting the process by zero leaves every coordinate unchanged; see
`Busemann/Frozen/Definitions/ProcessShift.lean:14-15`. -/
theorem processShift_zero (s : ProcessSample) : processShift 0 s = s := by
  apply Prod.ext
  · funext y
    simp [processShift, environmentTranslationEquiv_apply]
  · funext j x i
    simp [processShift]

/-- Shifting first by `w` and then by `z` equals one shift by `z + w`; see
`Busemann/Frozen/Definitions/ProcessShift.lean:14-15`. -/
theorem processShift_add (z w : Lattice) (s : ProcessSample) :
    processShift (z + w) s = processShift z (processShift w s) := by
  apply Prod.ext
  · funext y
    simp [processShift, environmentTranslationEquiv_apply, add_comm, add_left_comm]
  · funext j x i
    simp [processShift, add_comm, add_left_comm]

end LPP.Busemann
