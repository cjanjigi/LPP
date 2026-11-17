/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.FixedBoxCenteredDisplacements
public import Busemann.Process.LatticeMeshCellAverages
import Busemann.Process.ShiftTopology
import ProbabilityBasics.Analysis.FloorBoxCardinality
import Mathlib.Tactic

/-! Cell averages of actual centered cocycle displacements. -/

@[expose] public section

open MeasureTheory Filter LPPDifferentiability
open scoped BigOperators Topology

namespace LPP.Busemann

/-- Each cell of every fixed reciprocal mesh has vanishing normalized average
of canonical centered displacements. This is the fixed-cell normalization
in JR arXiv:1810.03580v3, Appendix B, B.6 to B.3. -/
theorem ae_tendsto_mesh_centered_cell_averages
    (P : Measure ProcessSample) [IsProbabilityMeasure P]
    (hShift : ∀ z : Lattice, MeasurePreserving (processShift z) P P)
    (B : Lattice → Lattice → ProcessSample → ℝ)
    (hB : is_shift_covariant_cocycle P processShift B)
    (hInt : ∀ x y, Integrable (B x y) P) :
    let mProc : MeasurableSpace ProcessSample := inferInstance
    let I : MeasurableSpace ProcessSample :=
      ⨅ z : Lattice, @MeasurableSpace.invariants ProcessSample mProc (processShift z)
    letI : MeasurableSpace ProcessSample := mProc
    let u : Fin 2 → ProcessSample → ℝ :=
      fun i => P[B 0 (finiteEdgeStep i) | I]
    let coord : Fin 2 → Lattice → ℤ := fun i x => if i = 0 then x.1 else x.2
    let Fbar : Lattice → ProcessSample → ℝ := fun x s =>
      B 0 x s - ∑ i : Fin 2, u i s * ((coord i x : ℤ) : ℝ)
    let δ : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1)
    let a : ℕ → ℕ → ℕ → ℤ := fun m k n =>
      ⌊(n : ℝ) * (k : ℝ) * δ m / 8⌋
    let R₁ : ℕ → ℕ → ℕ → Finset ℤ := fun m k n =>
      Finset.Ico (a m k n) (a m (k + 1) n)
    let R₂ : ℕ → (ℕ × ℕ) → ℕ → Finset Lattice := fun m k n =>
      (R₁ m k.1 n).product (R₁ m k.2 n)
    ∀ᵐ s ∂P,
      (∀ (m k : ℕ) (i : Fin 2), Tendsto (fun n : ℕ =>
        (∑ t ∈ R₁ m k n, Fbar (t • finiteEdgeStep i) s) /
          ((n : ℝ) * ((R₁ m k n).card : ℝ))) atTop (𝓝 0)) ∧
      (∀ (m : ℕ) (k : ℕ × ℕ), Tendsto (fun n : ℕ =>
        (∑ z ∈ R₂ m k n, Fbar z s) /
          ((n : ℝ) * ((R₂ m k n).card : ℝ))) atTop (𝓝 0)) := by
  exact ae_tendsto_mesh_centered_cell_averages_of_action P processShift processShift_zero processShift_add hShift B hB hInt

end LPP.Busemann
