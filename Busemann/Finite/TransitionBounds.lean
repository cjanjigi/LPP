/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Finite.PartitionRecursion
public import Busemann.Frozen.Definitions.FiniteEdgeStep
public import Busemann.Frozen.Definitions.FiniteTiltCoordinate
import Mathlib.Tactic

/-! Bounds for the two normalized first-departure terms of the actual finite partition. -/

public section

open LPPDifferentiability
open scoped BigOperators

namespace LPP.Busemann

/-- The two actual finite partition ratios are positive, below one, and sum to
one, as in the corrected departure-site normalization of
JR1810.03580v3, Appendix A.1. -/
theorem finite_tilted_partition_transition_bounds (ω : Environment)
    (h : ℝ × ℝ) (β : ℝ) (hβ : 0 < β) (N : ℕ) (x : Lattice) :
    let Z : ℕ → Lattice → ℝ := fun n y =>
      ∑ k : Fin (n + 1), ∑ q : LPPDifferentiability.Path y (k.val, n - k.val),
        Real.exp (β * (pathWeight ω q + h.1 * (k.val : ℝ) +
          h.2 * ((n - k.val : ℕ) : ℝ)))
    let p : Fin 2 → ℝ := fun i =>
      Real.exp (β * (ω x + finiteTiltCoordinate h i)) *
        Z N (x + finiteEdgeStep i) / Z (N + 1) x
    (∀ i, 0 < p i ∧ p i < 1) ∧ p 0 + p 1 = 1 := by
  classical
  let Z : ℕ → Lattice → ℝ := fun n y =>
    ∑ k : Fin (n + 1), ∑ q : LPPDifferentiability.Path y (k.val, n - k.val),
      Real.exp (β * (pathWeight ω q + h.1 * (k.val : ℝ) +
        h.2 * ((n - k.val : ℕ) : ℝ)))
  let p : Fin 2 → ℝ := fun i =>
    Real.exp (β * (ω x + finiteTiltCoordinate h i)) *
      Z N (x + finiteEdgeStep i) / Z (N + 1) x
  change (∀ i, 0 < p i ∧ p i < 1) ∧ p 0 + p 1 = 1

  -- Use the public actual partition positivity and first-departure recursion.
  have hparent := finite_tilted_partition_zero_pos_succ ω h β hβ N x
  have hrec : Z (N + 1) x = Real.exp (β * ω x) *
      (Real.exp (β * h.1) * Z N (x + (1, 0)) +
        Real.exp (β * h.2) * Z N (x + (0, 1))) := hparent.2.2
  have hparent_next := finite_tilted_partition_zero_pos_succ ω h β hβ (N + 1) x
  have hden : 0 < Z (N + 1) x := hparent_next.2.1
  have hleft : 0 < Z N (x + finiteEdgeStep 0) := by
    have hchild := finite_tilted_partition_zero_pos_succ ω h β hβ N
      (x + finiteEdgeStep 0)
    exact hchild.2.1
  have hright : 0 < Z N (x + finiteEdgeStep 1) := by
    have hchild := finite_tilted_partition_zero_pos_succ ω h β hβ N
      (x + finiteEdgeStep 1)
    exact hchild.2.1

  -- Each ratio is positive because its exponential and partition sums are positive.
  have hp0 : 0 < p 0 := by
    unfold p finiteTiltCoordinate
    simp only [Fin.val_zero, ite_true]
    exact div_pos (mul_pos (Real.exp_pos _) hleft) hden
  have hp1 : 0 < p 1 := by
    unfold p finiteTiltCoordinate
    simp only [Fin.val_one, one_ne_zero, ite_false]
    exact div_pos (mul_pos (Real.exp_pos _) hright) hden

  -- Expanding the departure weights gives exactly the public recursion numerator.
  have hnum :
      Real.exp (β * (ω x + h.1)) * Z N (x + finiteEdgeStep 0) +
        Real.exp (β * (ω x + h.2)) * Z N (x + finiteEdgeStep 1) = Z (N + 1) x := by
    rw [hrec]
    simp only [finiteEdgeStep, Fin.val_zero, Fin.val_one, ite_true, one_ne_zero,
      ite_false, mul_add, Real.exp_add]
    ring
  have hsum : p 0 + p 1 = 1 := by
    change
      (Real.exp (β * (ω x + h.1)) * Z N (x + finiteEdgeStep 0) /
        Z (N + 1) x) +
      (Real.exp (β * (ω x + h.2)) * Z N (x + finiteEdgeStep 1) /
        Z (N + 1) x) = 1
    rw [← add_div, hnum, div_self hden.ne']

  -- The other positive term makes each summand strictly smaller than their sum.
  have hlt0 : p 0 < 1 := by
    rw [← hsum]
    linarith
  have hlt1 : p 1 < 1 := by
    rw [← hsum]
    linarith
  constructor
  · intro i
    fin_cases i
    · exact ⟨hp0, hlt0⟩
    · exact ⟨hp1, hlt1⟩
  · exact hsum

end LPP.Busemann
