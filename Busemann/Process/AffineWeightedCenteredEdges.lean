/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Process.CenteredIncrementMeans
public import Busemann.Process.UnitActionRectangles
public import Busemann.Process.LatticeAffineWeightedCenteredEdges
public import ProbabilityBasics.Probability.RectangleAffineWeights
import ProbabilityBasics.Combinatorics.ColumnRectangle
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-! Native one- and two-coordinate affine averages of canonical centered edges. -/

@[expose] public section

open MeasureTheory Filter LPPDifferentiability
open scoped BigOperators Topology

namespace LPP.Busemann

/-- Canonically centered unit edges have vanishing affine averages along both
single-coordinate prefixes and every ordering of the two-coordinate prefixes.
This is the affine specialization of JR1810.03580v3, Appendix B, Lemma B.5. -/
theorem ae_tendsto_affine_weighted_centered_edges
    (P : Measure ProcessSample) [IsProbabilityMeasure P]
    (hShift : ∀ z : Lattice, MeasurePreserving (processShift z) P P)
    (B : Lattice → Lattice → ProcessSample → ℝ)
    (hB : is_shift_covariant_cocycle P processShift B)
    (hInt : ∀ x y, Integrable (B x y) P)
    (b : Fin 2 → ℝ) (hb : ∀ i, 0 < b i) :
    let mProc : MeasurableSpace ProcessSample := inferInstance
    let I : MeasurableSpace ProcessSample :=
      ⨅ z : Lattice, @MeasurableSpace.invariants ProcessSample mProc (processShift z)
    letI : MeasurableSpace ProcessSample := mProc
    let u : Fin 2 → ProcessSample → ℝ :=
      fun i => P[B 0 (finiteEdgeStep i) | I]
    let F : Fin 2 → ProcessSample → ℝ :=
      fun i s => B 0 (finiteEdgeStep i) s - u i s
    let R₁ : ℕ → Finset ℤ := fun n =>
      Finset.Ico 0 ((⌊(n : ℝ) * b 0⌋₊ : ℕ) : ℤ)
    let R₂ : ℕ → Finset (ℤ × ℤ) := fun n =>
      (R₁ n).product (Finset.Ico 0 ((⌊(n : ℝ) * b 1⌋₊ : ℕ) : ℤ))
    let κ : Fin 2 → (ℤ × ℤ) → ℤ := fun j k => if j = 0 then k.1 else k.2
    let X : Equiv.Perm (Fin 2) → (ℤ × ℤ) → Lattice :=
      fun σ k => k.1 • finiteEdgeStep (σ 0) + k.2 • finiteEdgeStep (σ 1)
    ∀ᵐ s ∂P,
      (∀ (i : Fin 2) (c d : ℝ), Tendsto (fun n : ℕ =>
        (∑ k ∈ R₁ n, (c + d * (((k + 1 : ℤ) : ℝ) / (n : ℝ))) *
          F i (processShift (k • finiteEdgeStep i) s)) / (n : ℝ))
        atTop (𝓝 0)) ∧
      (∀ (σ : Equiv.Perm (Fin 2)) (j : Fin 2) (c d : ℝ),
        Tendsto (fun n : ℕ =>
          (∑ k ∈ R₂ n, (c + d * (((κ j k + 1 : ℤ) : ℝ) / (n : ℝ))) *
            F (σ j) (processShift (X σ k) s)) / (n : ℝ)^2)
          atTop (𝓝 0)) := by
  simpa only [latticeInvariantSigma] using
    (ae_tendsto_affine_weighted_centered_edges_of_action
      (Ω := ProcessSample) P processShift processShift_zero processShift_add
      hShift B hB hInt b hb)

end LPP.Busemann
