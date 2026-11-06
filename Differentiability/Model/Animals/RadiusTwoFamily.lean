/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.Animals.ExcessSumCover
public import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Tactic

/-! The supremum over every admissible radius-two animal, and its characterization by
uniform positive epsilons. No new maximum or default is defined. -/

public section
open Filter Set
open scoped Topology BigOperators
namespace LPPDifferentiability

/-- The extended supremum over all admissible finite sets has exactly the uniform
epsilon-eventual upper-bound meaning. -/
theorem limsup_iSup_radiusTwoAnimal_le_iff (Z : Lattice → ℝ) (C : ℝ) :
    (limsup (fun N : ℕ =>
      ⨆ A : {A : Finset Lattice // (0 : Lattice) ∈ A ∧ A.card ≤ N+1 ∧
        ((SimpleGraph.fromRel (fun x y : Lattice =>
          |x.1-y.1| ≤ 2 ∧ |x.2-y.2| ≤ 2)).induce (↑A : Set Lattice)).Connected},
        (((∑ b ∈ A.val, Z b) / (N:ℝ) : ℝ) : EReal)) atTop ≤ (C : EReal)) ↔
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ A : Finset Lattice, (0 : Lattice) ∈ A → A.card ≤ N+1 →
        ((SimpleGraph.fromRel (fun x y : Lattice =>
          |x.1-y.1| ≤ 2 ∧ |x.2-y.2| ≤ 2)).induce (↑A : Set Lattice)).Connected →
        (∑ b ∈ A, Z b) / (N:ℝ) < C+ε := by
  constructor
  · intro h ε hε
    have he := eventually_lt_of_limsup_lt
      (h.trans_lt (EReal.coe_lt_coe_iff.mpr (lt_add_of_pos_right C hε)))
    filter_upwards [he] with N hN
    intro A hzero hcard hconn
    apply EReal.coe_lt_coe_iff.mp
    exact (le_iSup (fun A : {A : Finset Lattice //
      (0 : Lattice) ∈ A ∧ A.card ≤ N+1 ∧
      ((SimpleGraph.fromRel (fun x y : Lattice =>
        |x.1-y.1| ≤ 2 ∧ |x.2-y.2| ≤ 2)).induce (↑A : Set Lattice)).Connected} =>
        (((∑ b ∈ A.val, Z b) / (N:ℝ) : ℝ) : EReal))
      ⟨A,hzero,hcard,hconn⟩).trans_lt hN
  · intro h
    apply EReal.le_of_forall_lt_iff_le.mp
    intro c hc
    have hCc : C < c := EReal.coe_lt_coe_iff.mp hc
    have he := h (c-C) (sub_pos.mpr hCc)
    apply limsup_le_of_le (by isBoundedDefault)
    filter_upwards [he] with N hN
    apply iSup_le
    rintro ⟨A,hzero,hcard,hconn⟩
    exact EReal.coe_le_coe_iff.mpr (by
      have hb := (hN A hzero hcard hconn).le
      linarith only [hb])

end LPPDifferentiability
