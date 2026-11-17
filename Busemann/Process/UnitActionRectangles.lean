/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Frozen.Definitions.FiniteEdgeStep
public import Busemann.Process.LatticeUnitActionRectangles
public import Busemann.Process.ShiftTopology
public import Mathlib.MeasureTheory.MeasurableSpace.Invariants

/-! The invariant sigma algebra of a column action is the one-step invariant sigma algebra. -/

@[expose] public section

open MeasureTheory LPPDifferentiability

namespace LPP.Busemann

/-- Invariance under all signed shifts in one coordinate is exactly invariance under its unit shift.
This uses the literal shift action in `Busemann/Frozen/Definitions/ProcessShift.lean:14-15`. -/
theorem unit_column_invariants (i : Fin 2) :
    let mProc : MeasurableSpace ProcessSample := inferInstance
    let e : Lattice := finiteEdgeStep i
    let T : Lattice → ProcessSample → ProcessSample :=
      fun z s => processShift (z.1 • e) s
    let I : MeasurableSpace ProcessSample :=
      ⨅ z : Lattice, @MeasurableSpace.invariants ProcessSample mProc (T z)
    let J : MeasurableSpace ProcessSample :=
      @MeasurableSpace.invariants ProcessSample mProc (processShift e)
    I = J := by
  classical
  let mProc : MeasurableSpace ProcessSample := inferInstance
  let e : Lattice := finiteEdgeStep i
  let T : Lattice → ProcessSample → ProcessSample :=
    fun z s => processShift (z.1 • e) s
  let I : MeasurableSpace ProcessSample :=
    ⨅ z : Lattice, @MeasurableSpace.invariants ProcessSample mProc (T z)
  let J : MeasurableSpace ProcessSample :=
    @MeasurableSpace.invariants ProcessSample mProc (processShift e)
  let : MeasurableSpace ProcessSample := mProc
  change I = J
  exact unit_column_invariants_of_action processShift processShift_zero processShift_add i

end LPP.Busemann
