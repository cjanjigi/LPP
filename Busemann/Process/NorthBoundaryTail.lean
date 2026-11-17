/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.Definitions.Additive
public import LPP_Foundations.Model.LastPassage.Axes
import LPP_Foundations.Model.LocalDefectPath
import Mathlib.Data.Int.Order.Basic

/-! The horizontal passage along the modified north boundary is an additive edge sum. -/

@[expose] public section

open scoped BigOperators
open LPPDifferentiability LPP.Busemann

namespace LPP.Busemann

/-- Replacing the collected top-row weights by their rightward cocycle edges
makes the horizontal passage equal to the cocycle increment. This is the north
boundary tail identity of GRS 1510.00859v2, Section 5.2, formula (6.8), using
the axis sum and finite edge telescope (`Axes.lean:68-71`,
`LocalDefectPath.lean:24-29`). -/
theorem north_boundary_horizontal_passage_eq_cocycle
    (ω : Environment) (C : Lattice → Lattice → ℝ)
    (hC : is_additive C) (v : Lattice) (k : ℕ) :
    let N : Environment := fun z =>
      if z.2 = v.2 ∧ z.1 < v.1 then C z (z + (1, 0)) else ω z
    lastPassage N (v - ((k : ℤ), 0)) (k, 0) =
      C (v - ((k : ℤ), 0)) v := by
  let x : Lattice := v - ((k : ℤ), 0)
  let N : Environment := fun z =>
    if z.2 = v.2 ∧ z.1 < v.1 then C z (z + (1, 0)) else ω z
  change lastPassage N x (k, 0) = C x v
  change ∀ a b c : Lattice, C a b + C b c = C a c at hC
  -- Use the horizontal sequence from the translated start through the endpoint.
  let axisVertex : Fin (k + 1) → Lattice :=
    fun i => (x.1 + (i.val : ℤ), x.2)
  have hstart : axisVertex 0 = x := by
    apply Prod.ext
    · simp [axisVertex]
    · rfl
  have hfinish : axisVertex (Fin.last k) = v := by
    apply Prod.ext
    · simp only [axisVertex, Fin.val_last]
      change (v.1 - (k : ℤ)) + (k : ℤ) = v.1
      exact sub_add_cancel _ _
    · simp only [axisVertex]
      simp [x]
  -- Consecutive indices describe one rightward edge.
  have hstep (i : Fin k) :
      axisVertex i.succ = axisVertex i.castSucc + (1, 0) := by
    simp only [axisVertex, Fin.val_succ, Fin.val_castSucc]
    apply Prod.ext
    · rw [Nat.cast_add, Nat.cast_one]
      exact (add_assoc x.1 (i.val : ℤ) 1).symm
    · exact (add_zero x.2).symm
  -- Every collected site is on the changed row and strictly left of the endpoint.
  have hterm (i : Fin k) :
      N (x.1 + (i.val : ℤ), x.2) =
        C (axisVertex i.castSucc) (axisVertex i.succ) := by
    let z : Lattice := (x.1 + (i.val : ℤ), x.2)
    have hiCast : (i.val : ℤ) < (k : ℤ) := Int.ofNat_lt.mpr i.isLt
    have hrow : z.2 = v.2 := by simp [z, x]
    have hleft : z.1 < v.1 := by
      change (v.1 - (k : ℤ)) + (i.val : ℤ) < v.1
      calc
        (v.1 - (k : ℤ)) + (i.val : ℤ) <
            (v.1 - (k : ℤ)) + (k : ℤ) :=
          add_lt_add_right hiCast _
        _ = v.1 := sub_add_cancel _ _
    have hmodify : N z = C z (z + (1, 0)) := by
      simp [N, hrow, hleft]
    have hvertex : axisVertex i.castSucc = z := rfl
    have hedge : z + (1, 0) = axisVertex i.succ := by
      calc
        z + (1, 0) = axisVertex i.castSucc + (1, 0) :=
          congrArg (fun y : Lattice => y + (1, 0)) hvertex.symm
        _ = axisVertex i.succ := (hstep i).symm
    calc
      N (x.1 + (i.val : ℤ), x.2) = N z := rfl
      _ = C z (z + (1, 0)) := hmodify
      _ = C (axisVertex i.castSucc) (z + (1, 0)) :=
        congrArg (fun y : Lattice => C y (z + (1, 0))) hvertex.symm
      _ = C (axisVertex i.castSucc) (axisVertex i.succ) :=
        congrArg (C (axisVertex i.castSucc)) hedge
  calc
    lastPassage N x (k, 0) =
        ∑ i : Fin k, N (x.1 + (i.val : ℤ), x.2) :=
      LPPDifferentiability.lastPassage_horizontal N x k
    _ = ∑ i : Fin k, C (axisVertex i.castSucc) (axisVertex i.succ) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hterm i
    _ = C (axisVertex 0) (axisVertex (Fin.last k)) :=
      LPP.finite_edge_potential_telescope k C hC axisVertex
    _ = C x v := by rw [hstart, hfinish]

end LPP.Busemann
