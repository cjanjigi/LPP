/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.DirectionalConditionalMeans
public import Busemann.Process.LatticeCenteredIncrementMeans
import Busemann.Process.ShiftTopology
import Mathlib.Tactic

/-! Conditional centering under the full and directional shift actions. -/

@[expose] public section

open MeasureTheory Filter LPPDifferentiability
open scoped Topology

namespace LPP.Busemann

/-- The literal full-action centered unit increment is measurable and integrable,
and has zero conditional mean under both the full and unit-shift invariant
sigma algebras. This is the centering step before JR arXiv:1810.03580v3,
Appendix B, Lemma B.5. -/
theorem centered_increment_condExp_zero
    (P : Measure ProcessSample) [IsProbabilityMeasure P]
    (hShift : ∀ z : Lattice, MeasurePreserving (processShift z) P P)
    (B : Lattice → Lattice → ProcessSample → ℝ)
    (hB : is_shift_covariant_cocycle P processShift B)
    (hInt : ∀ x y, Integrable (B x y) P) (i : Fin 2) :
    let mProc : MeasurableSpace ProcessSample := inferInstance
    let I : MeasurableSpace ProcessSample :=
      ⨅ z : Lattice, @MeasurableSpace.invariants ProcessSample mProc (processShift z)
    let e : Lattice := finiteEdgeStep i
    let J : MeasurableSpace ProcessSample :=
      @MeasurableSpace.invariants ProcessSample mProc (processShift e)
    letI : MeasurableSpace ProcessSample := mProc
    let φ : ProcessSample → ℝ := fun s => B 0 e s - P[B 0 e | I] s
    Measurable φ ∧ Integrable φ P ∧
      P[φ | I] =ᵐ[P] (0 : ProcessSample → ℝ) ∧
      P[φ | J] =ᵐ[P] (0 : ProcessSample → ℝ) := by
  simpa only [latticeInvariantSigma] using
    (centered_increment_condExp_zero_of_action
      (Ω := ProcessSample) P processShift processShift_zero processShift_add
      hShift B hB hInt i)

end LPP.Busemann
