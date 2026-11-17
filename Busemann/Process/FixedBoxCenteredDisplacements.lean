/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.AffineWeightedCenteredEdges
public import Busemann.Process.InvariantConditionalDrifts
public import Busemann.Process.CenteredDisplacementSums
public import Mathlib.Analysis.SpecificLimits.Basic
public import Busemann.Process.LatticeFixedBoxCenteredDisplacements
import Busemann.Process.ShiftTopology
import Mathlib.Tactic

/-! Fixed-box averages of canonically centered cocycle displacements. -/
@[expose] public section
open MeasureTheory Filter LPPDifferentiability
open scoped BigOperators Topology
namespace LPP.Busemann

/-- Fixed one- and two-coordinate boxes have vanishing averages of the actual
canonical centered displacements; JR1810.03580v3, Appendix B, Lemma B.6. -/
theorem ae_tendsto_fixed_box_centered_displacements
    (P : Measure ProcessSample) [IsProbabilityMeasure P]
    (hShift : ∀ z : Lattice, MeasurePreserving (processShift z) P P)
    (B : Lattice → Lattice → ProcessSample → ℝ)
    (hB : is_shift_covariant_cocycle P processShift B)
    (hInt : ∀ x y, Integrable (B x y) P)
    (a b : Fin 2 → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hab : ∀ j, a j < b j) :
    let mProc : MeasurableSpace ProcessSample := inferInstance
    let I : MeasurableSpace ProcessSample :=
      ⨅ z : Lattice, @MeasurableSpace.invariants ProcessSample mProc (processShift z)
    letI : MeasurableSpace ProcessSample := mProc
    let u : Fin 2 → ProcessSample → ℝ :=
      fun i => P[B 0 (finiteEdgeStep i) | I]
    let coord : Fin 2 → Lattice → ℤ := fun i x => if i = 0 then x.1 else x.2
    let Fbar : Lattice → ProcessSample → ℝ := fun x s =>
      B 0 x s - ∑ i : Fin 2, u i s * ((coord i x : ℤ) : ℝ)
    let Q : Fin 2 → ℕ → Finset ℤ := fun j n =>
      Finset.Ico ((⌊(n : ℝ) * a j⌋₊ : ℕ) : ℤ)
        ((⌊(n : ℝ) * b j⌋₊ : ℕ) : ℤ)
    let X : Equiv.Perm (Fin 2) → (ℤ × ℤ) → Lattice :=
      fun σ k => k.1 • finiteEdgeStep (σ 0) + k.2 • finiteEdgeStep (σ 1)
    ∀ᵐ s ∂P,
      (∀ i : Fin 2, Tendsto (fun n : ℕ =>
        (∑ k ∈ Q 0 n, Fbar (k • finiteEdgeStep i) s) / (n : ℝ)^2)
        atTop (𝓝 0)) ∧
      (∀ σ : Equiv.Perm (Fin 2), Tendsto (fun n : ℕ =>
        (∑ k ∈ (Q 0 n).product (Q 1 n), Fbar (X σ k) s) / (n : ℝ)^3)
        atTop (𝓝 0)) := by
  exact ae_tendsto_fixed_box_centered_displacements_of_action P processShift processShift_zero processShift_add hShift B hB hInt a b ha hab

end LPP.Busemann
