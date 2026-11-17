/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.LatticeCocycleShellShape
import Busemann.Process.ShiftTopology

public import Busemann.Frozen.Definitions.RecoveryAE
public import Busemann.Process.MeshCellAverages
public import Busemann.Process.RealShortWeightWindows
import Busemann.Process.ShellLowerComparison
import Busemann.Process.ShellUpperComparison
import Mathlib.Tactic

/-! The native recovering-cocycle shape estimate on nonnegative lattice shells. -/
@[expose] public section
open MeasureTheory Filter LPPDifferentiability
open scoped BigOperators ENNReal Topology
namespace LPP.Busemann

/-- A stationary recovering cocycle with the original iid absolute p>2 weight
marginal has sublinear centered fluctuations uniformly on each native shell.
This is the shell conclusion in JR1810.03580v3, Appendix B, Theorem B.3. -/
theorem ae_uniform_recovering_cocycle_shell_shape
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    (P : Measure ProcessSample) [IsProbabilityMeasure P]
    (hMarginal : P.map processEnvironment = environmentLaw μ)
    (hShift : ∀ z : Lattice, MeasurePreserving (processShift z) P P)
    (B : Lattice → Lattice → ProcessSample → ℝ)
    (hB : is_shift_covariant_cocycle P processShift B)
    (hInt : ∀ x y, Integrable (B x y) P)
    (hRec : recovers_weight_map_ae P processEnvironment B) :
    let mProc : MeasurableSpace ProcessSample := inferInstance
    let I : MeasurableSpace ProcessSample :=
      ⨅ z : Lattice, @MeasurableSpace.invariants ProcessSample mProc (processShift z)
    letI : MeasurableSpace ProcessSample := mProc
    let u : Fin 2 → ProcessSample → ℝ :=
      fun i => P[B 0 (finiteEdgeStep i) | I]
    let S : ℕ → Finset Lattice := fun n => insert ((n : ℤ), 0)
      (((Finset.Icc (0 : ℤ) (n : ℤ)).product
        (Finset.Icc (0 : ℤ) (n : ℤ))).filter
          (fun x => x.1 + x.2 = (n : ℤ)))
    ∀ᵐ s ∂P, Tendsto (fun n : ℕ =>
      (S n).sup' (by dsimp [S]; exact Finset.insert_nonempty _ _)
        (fun x => |B 0 x s -
          (u 0 s * (x.1 : ℝ) + u 1 s * (x.2 : ℝ))|) / (n : ℝ))
      atTop (𝓝 0) := by
  exact ae_uniform_recovering_cocycle_shell_shape_of_action μ hmoment P processShift processEnvironment measurable_fst hMarginal processShift_zero processShift_add hShift B hB hInt hRec

end LPP.Busemann
