/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.Definitions.RandomCocycle
public import Busemann.Frozen.Definitions.ProcessShift
public import Busemann.Frozen.Definitions.FiniteEdgeStep
public import ProbabilityBasics.Probability.BirkhoffL1
import ProbabilityBasics.Probability.IdentDistribSublinear
import Busemann.Process.ShiftTopology
import Busemann.Process.LatticeDirectionalDrifts
import Mathlib.Tactic

/-! Directional drifts invariant under the full process action: JR1810.03580v3, Lemma B.4. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set LPPDifferentiability
open scoped Topology

namespace LPP.Busemann

/-- An arbitrary integrable stationary cocycle has one pair of random directional
drifts with literal displacement limits, L1 convergence and exact full-action
invariant representatives. This is the boundary argument of JR1810.03580v3,
Appendix B, Lemma B.4, without an ergodicity or deterministic-drift assumption. -/
theorem exists_full_action_directional_drifts
    (P : Measure ProcessSample) [IsProbabilityMeasure P]
    (hShift : ∀ z : Lattice, MeasurePreserving (processShift z) P P)
    (B : Lattice → Lattice → ProcessSample → ℝ)
    (hB : is_shift_covariant_cocycle P processShift B)
    (hInt : ∀ x y, Integrable (B x y) P) :
    ∃ u : Fin 2 → ProcessSample → ℝ,
      (∀ i : Fin 2, Measurable (u i) ∧ Integrable (u i) P ∧
        (∀ᵐ s ∂P, Tendsto (fun n : ℕ =>
          B 0 (n • finiteEdgeStep i) s / (n : ℝ)) atTop (𝓝 (u i s))) ∧
        (∫ s, u i s ∂P) = ∫ s, B 0 (finiteEdgeStep i) s ∂P ∧
        Tendsto (fun n : ℕ => ∫ s,
          |B 0 (n • finiteEdgeStep i) s / (n : ℝ) - u i s| ∂P)
          atTop (𝓝 0)) ∧
      ∀ (i : Fin 2) (z : Lattice) (s : ProcessSample),
        u i (processShift z s) = u i s := by
  exact exists_full_action_directional_drifts_of_action
    P processShift processShift_zero processShift_add hShift B hB hInt

end LPP.Busemann
