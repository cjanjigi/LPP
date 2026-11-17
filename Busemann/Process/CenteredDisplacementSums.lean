/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Frozen.Definitions.Additive
public import Busemann.Frozen.Definitions.FiniteEdgeStep
public import ProbabilityBasics.Analysis.TriangularPrefixSum
import Mathlib.Tactic

/-! Actual translated cocycle prefixes and their finite edge weights. -/

@[expose] public section
open LPPDifferentiability
open scoped BigOperators
namespace LPP.Busemann

/-- Summing a translated additive-ray displacement prefix gives the exact weighted
edge sum. This is the finite cocycle step in JR1810.03580v3, Appendix B, Lemma B.6. -/
theorem sum_additive_ray_prefix_eq_weighted_edges
    (C : Lattice → Lattice → ℝ) (hC : is_additive C)
    (f : Fin 2 → Lattice → ℝ)
    (hEdge : ∀ (x : Lattice) (i : Fin 2), C x (x + finiteEdgeStep i) = f i x)
    (z : Lattice) (i : Fin 2) (m : ℕ) :
    (∑ k ∈ Finset.range m, C z (z + (k : ℤ) • finiteEdgeStep i)) =
      ∑ j ∈ Finset.range m, ((m : ℝ) - (j : ℝ) - 1) *
        f i (z + (j : ℤ) • finiteEdgeStep i) := by
  have htel (q : ℕ) : C z (z + (q : ℤ) • finiteEdgeStep i) =
      ∑ j ∈ Finset.range q, f i (z + (j : ℤ) • finiteEdgeStep i) := by
    induction q with
    | zero =>
      have hz : C z z = 0 := by have hh := hC z z z; linarith only [hh]
      simpa only [Nat.cast_zero, zero_zsmul, add_zero, Finset.range_zero,
        Finset.sum_empty] using hz
    | succ q ih =>
      have hend : z + ((q + 1 : ℕ) : ℤ) • finiteEdgeStep i =
          (z + (q : ℤ) • finiteEdgeStep i) + finiteEdgeStep i := by
        simp only [Nat.cast_add, Nat.cast_one, add_zsmul, one_zsmul, add_assoc]
      rw [hend, ← hC z (z + (q : ℤ) • finiteEdgeStep i)
        ((z + (q : ℤ) • finiteEdgeStep i) + finiteEdgeStep i), hEdge, ih]
      exact (Finset.sum_range_succ _ q).symm
  simp_rw [htel]
  exact ProbabilityBasics.sum_range_sum_range_eq_sum_weighted
    (fun j : ℕ => f i (z + (j : ℤ) • finiteEdgeStep i)) m

end LPP.Busemann
