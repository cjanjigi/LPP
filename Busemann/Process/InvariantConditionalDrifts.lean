/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Process.DirectionalDrifts
public import Busemann.Process.LatticeInvariantConditionalDrifts
public import Mathlib.MeasureTheory.MeasurableSpace.Invariants
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Busemann.Process.ShiftTopology
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-! The full-action directional drift is the invariant conditional mean. -/

@[expose] public section

open MeasureTheory Filter LPPDifferentiability
open scoped Topology

namespace LPP.Busemann

/-- The same full-action invariant directional drifts are the conditional means
of the actual unit increments under the full invariant sigma-algebra. This is
JR1810.03580v3, Appendix B, Lemma B.4; no ergodicity is assumed. -/
theorem exists_full_action_directional_drifts_condExp
    (P : Measure ProcessSample) [IsProbabilityMeasure P]
    (hShift : ∀ z : Lattice, MeasurePreserving (processShift z) P P)
    (B : Lattice → Lattice → ProcessSample → ℝ)
    (hB : is_shift_covariant_cocycle P processShift B)
    (hInt : ∀ x y, Integrable (B x y) P) :
    let mProc : MeasurableSpace ProcessSample := inferInstance
    let I : MeasurableSpace ProcessSample :=
      ⨅ z : Lattice, @MeasurableSpace.invariants ProcessSample mProc (processShift z)
    letI : MeasurableSpace ProcessSample := mProc
    ∃ u : Fin 2 → ProcessSample → ℝ,
      ((∀ i : Fin 2,
        Measurable (u i) ∧ Integrable (u i) P ∧
        (∀ᵐ s ∂P, Tendsto
          (fun n : ℕ => B 0 (n • finiteEdgeStep i) s / (n : ℝ))
          atTop (𝓝 (u i s))) ∧
        (∫ s, u i s ∂P) = ∫ s, B 0 (finiteEdgeStep i) s ∂P ∧
        Tendsto (fun n : ℕ => ∫ s,
          |B 0 (n • finiteEdgeStep i) s / (n : ℝ) - u i s| ∂P)
          atTop (𝓝 0)) ∧
       (∀ (i : Fin 2) (z : Lattice) (s : ProcessSample),
         u i (processShift z s) = u i s)) ∧
      (∀ i : Fin 2, u i =ᵐ[P] P[B 0 (finiteEdgeStep i) | I]) := by
  let generic := exists_full_action_directional_drifts_condExp_of_action
    (Ω := ProcessSample) P processShift processShift_zero processShift_add
    hShift B hB hInt
  exact
    (show
    let mProc : MeasurableSpace ProcessSample := inferInstance
    let I : MeasurableSpace ProcessSample :=
      ⨅ z : Lattice, @MeasurableSpace.invariants ProcessSample mProc (processShift z)
    letI : MeasurableSpace ProcessSample := mProc
    ∃ u : Fin 2 → ProcessSample → ℝ,
      ((∀ i : Fin 2,
        Measurable (u i) ∧ Integrable (u i) P ∧
        (∀ᵐ s ∂P, Tendsto
          (fun n : ℕ => B 0 (n • finiteEdgeStep i) s / (n : ℝ))
          atTop (𝓝 (u i s))) ∧
        (∫ s, u i s ∂P) = ∫ s, B 0 (finiteEdgeStep i) s ∂P ∧
        Tendsto (fun n : ℕ => ∫ s,
          |B 0 (n • finiteEdgeStep i) s / (n : ℝ) - u i s| ∂P)
          atTop (𝓝 0)) ∧
       (∀ (i : Fin 2) (z : Lattice) (s : ProcessSample),
         u i (processShift z s) = u i s)) ∧
      (∀ i : Fin 2, u i =ᵐ[P] P[B 0 (finiteEdgeStep i) | I])
      from by
        simpa only [latticeInvariantSigma] using generic)
end LPP.Busemann
