/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.Definitions.Additive
public import Busemann.Frozen.Definitions.FiniteEdgeStep
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Int.Interval
import Mathlib.Tactic

/-! Shared finite shell bounds from the proof of Appendix B, B.3 in JR1810.03580v3. -/

@[expose] public section

open LPPDifferentiability
open scoped BigOperators

namespace LPP.Busemann

/-- Membership in the finite signed ball is exactly the stated sum of coordinate absolute values.
This is the finite set argument in JR1810.03580v3, Appendix B, proof of B.3. -/
theorem signed_ball_mem (n : ℕ) (z : Lattice) :
    z ∈ insert 0
      (((Finset.Icc (-(2 * (n : ℤ))) (2 * (n : ℤ))).product
        (Finset.Icc (-(2 * (n : ℤ))) (2 * (n : ℤ)))).filter
          (fun z => z.1.natAbs + z.2.natAbs ≤ 2 * n)) ↔
      z.1.natAbs + z.2.natAbs ≤ 2 * n := by
  constructor
  · intro hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · simp
    · exact (Finset.mem_filter.mp hz).2
  · intro hz
    have h1 : |z.1| ≤ (2 * n : ℕ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast (show z.1.natAbs ≤ 2 * n by omega)
    have h2 : |z.2| ≤ (2 * n : ℕ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast (show z.2.natAbs ≤ 2 * n by omega)
    apply Finset.mem_insert_of_mem
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hz⟩
    · exact Finset.mem_Icc.mpr (by simpa using (abs_le.mp h1))
    · exact Finset.mem_Icc.mpr (by simpa using (abs_le.mp h2))

/-- Additivity and a bound on each unit step bound any finite coordinate ray by
the sum of the stepwise absolute bounds. This is the finite ray argument in
JR1810.03580v3, Appendix B, proof of B.3. -/
theorem additive_ray_upper
    (A : Lattice → Lattice → ℝ) (hA : is_additive A)
    (V : Fin 2 → Lattice → ℝ)
    (hUpper : ∀ (z : Lattice) (i : Fin 2), A z (z + finiteEdgeStep i) ≤ V i z)
    (z : Lattice) (i : Fin 2) (q : ℕ) :
    A z (z + (q : ℤ) • finiteEdgeStep i) ≤
      ∑ t ∈ Finset.range q, |V i (z + (t : ℤ) • finiteEdgeStep i)| := by
  induction q with
  | zero =>
    have hzero : A z z = 0 := by have hh := hA z z z; linarith only [hh]
    simpa only [Nat.cast_zero, zero_zsmul, add_zero, Finset.range_zero,
      Finset.sum_empty] using hzero.le
  | succ q ih =>
    have hend : z + ((q + 1 : ℕ) : ℤ) • finiteEdgeStep i =
        (z + (q : ℤ) • finiteEdgeStep i) + finiteEdgeStep i := by
      simp only [Nat.cast_add, Nat.cast_one, add_zsmul, one_zsmul, add_assoc]
    rw [hend, ← hA z (z + (q : ℤ) • finiteEdgeStep i)
      ((z + (q : ℤ) • finiteEdgeStep i) + finiteEdgeStep i)]
    exact (add_le_add ih ((hUpper _ i).trans (le_abs_self _))).trans_eq
      (Finset.sum_range_succ _ q).symm

end LPP.Busemann
