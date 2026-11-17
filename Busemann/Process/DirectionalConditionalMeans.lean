/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.InvariantConditionalDrifts
public import Busemann.Process.LatticeDirectionalConditionalMeans
import Busemann.Process.ShiftTopology
import ProbabilityBasics.Probability.BirkhoffInvariantSetIntegrals
import Mathlib.Tactic

/-! Conditional means for a directional shift and the full shift action. -/

@[expose] public section

open MeasureTheory Filter LPPDifferentiability
open scoped Topology

namespace LPP.Busemann

/-- A unit increment has the same conditional mean under its unit-shift
invariants as under the full signed-action invariants. This is the directional
bridge from JR arXiv:1810.03580v3, Appendix B, Lemma B.4 and (B.2). -/
theorem directional_condExp_eq_full_action_condExp
    (P : Measure ProcessSample) [IsProbabilityMeasure P]
    (hShift : ∀ z : Lattice, MeasurePreserving (processShift z) P P)
    (B : Lattice → Lattice → ProcessSample → ℝ)
    (hB : is_shift_covariant_cocycle P processShift B)
    (hInt : ∀ x y, Integrable (B x y) P) :
    let mProc : MeasurableSpace ProcessSample := inferInstance
    let I : MeasurableSpace ProcessSample :=
      ⨅ z : Lattice, @MeasurableSpace.invariants ProcessSample mProc (processShift z)
    let J : Fin 2 → MeasurableSpace ProcessSample := fun i =>
      @MeasurableSpace.invariants ProcessSample mProc (processShift (finiteEdgeStep i))
    letI : MeasurableSpace ProcessSample := mProc
    ∀ i : Fin 2,
      P[B 0 (finiteEdgeStep i) | J i] =ᵐ[P]
        P[B 0 (finiteEdgeStep i) | I] := by
  let generic := directional_condExp_eq_full_action_condExp_of_action
    (Ω := ProcessSample) P processShift processShift_zero processShift_add
    hShift B hB hInt
  exact
    (show
    let mProc : MeasurableSpace ProcessSample := inferInstance
    let I : MeasurableSpace ProcessSample :=
      ⨅ z : Lattice, @MeasurableSpace.invariants ProcessSample mProc (processShift z)
    let J : Fin 2 → MeasurableSpace ProcessSample := fun i =>
      @MeasurableSpace.invariants ProcessSample mProc (processShift (finiteEdgeStep i))
    letI : MeasurableSpace ProcessSample := mProc
    ∀ i : Fin 2,
      P[B 0 (finiteEdgeStep i) | J i] =ᵐ[P]
        P[B 0 (finiteEdgeStep i) | I]
      from by
        simpa only [latticeInvariantSigma] using generic)
end LPP.Busemann
