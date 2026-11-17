/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Frozen.Definitions.ProcessEnvironment
public import Busemann.Frozen.Definitions.ProcessShift
public import Busemann.Frozen.Definitions.RandomCocycle
public import Busemann.Frozen.Definitions.RecoveryAE
public import Busemann.Frozen.Definitions.SupportTilt
import Mathlib.Tactic

/-! Convert one common full-event family to the fixed-tilt cocycle and recovery predicates. -/

@[expose] public section

open MeasureTheory Filter LPPDifferentiability

namespace LPP.Busemann

/-- A common full event gives the almost-everywhere cocycle and recovery predicates at each tilt.
This is the conditional conversion used with the full-event clauses of JR1810.03580v3,
Theorem 4.8; it preserves the supplied measure, field, and event. -/
theorem cocycle_and_recovery_ae_of_full_event
    (g : Quadrant → ℝ) (P : Measure ProcessSample) [IsProbabilityMeasure P]
    (B : SupportTilt g → Lattice → Lattice → ProcessSample → ℝ)
    (C : Set ProcessSample) (hCMeas : MeasurableSet C) (hCProb : P C = 1)
    (hMeas : Measurable (fun q : SupportTilt g × (Lattice × (Lattice × ProcessSample)) =>
      B q.1 q.2.1 q.2.2.1 q.2.2.2))
    (hOnC : ∀ s ∈ C, ∀ h : SupportTilt g, ∀ x y z : Lattice,
      B h (x + z) (y + z) s = B h x y (processShift z s) ∧
      B h x y s + B h y z s = B h x z s)
    (hRec : ∀ s ∈ C, ∀ h : SupportTilt g,
      recovers_environment (processEnvironment s) (fun x y => B h x y s)) :
    ∀ h : SupportTilt g,
      is_shift_covariant_cocycle P processShift (B h) ∧
      recovers_weight_map_ae P processEnvironment (B h) := by
  have hCAE : ∀ᵐ s ∂P, s ∈ C :=
    (mem_ae_iff_prob_eq_one hCMeas).mpr hCProb
  intro h
  have hBMeas : Measurable (fun p : (Lattice × Lattice) × ProcessSample =>
      B h p.1.1 p.1.2 p.2) := by
    have hEmbedding : Measurable (fun p : (Lattice × Lattice) × ProcessSample =>
        (h, (p.1.1, (p.1.2, p.2)))) := by
      fun_prop
    exact hMeas.comp hEmbedding
  have hAdd : ∀ᵐ s ∂P, is_additive (fun x y => B h x y s) := by
    filter_upwards [hCAE] with s hs
    intro x y z
    exact (hOnC s hs h x y z).2
  have hRecovery : ∀ᵐ s ∂P,
      recovers_environment (processEnvironment s) (fun x y => B h x y s) := by
    filter_upwards [hCAE] with s hs
    exact hRec s hs h
  refine ⟨?_, hRecovery⟩
  refine ⟨hBMeas, ?_, hAdd⟩
  intro x y z
  filter_upwards [hCAE] with s hs
  exact (hOnC s hs h x y z).1

end LPP.Busemann
