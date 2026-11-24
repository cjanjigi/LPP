/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.FinalDraft.Contour.BoundaryIndex
import LPP_Foundations.Model.ClosedLatticeWalkCounts
import Mathlib.Tactic

/-! The two sets of distinct neighboring cells from the final draft's contour lemma. -/

public section

namespace LPPDifferentiability

private theorem up_edge_from_left {e : Lattice × Lattice} (h : e.2 - e.1 = (0, 1)) :
    e = (( (dualEdgeLeftCellCode e).1 + 1, (dualEdgeLeftCellCode e).2),
      ((dualEdgeLeftCellCode e).1 + 1, (dualEdgeLeftCellCode e).2 + 1)) ∧
      dualEdgeRightCellCode e = dualEdgeLeftCellCode e + (1, 0) := by
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := e
  change c - a = 0 at hx
  change d - b = 1 at hy
  have hc : c = a := by omega
  have hd : d = b + 1 := by omega
  subst c d
  rw [(dual_cells_of_up a b).1, (dual_cells_of_up a b).2]
  simp only [sub_add_cancel, Prod.mk_add_mk, add_zero, and_self]

private theorem left_edge_from_left {e : Lattice × Lattice} (h : e.2 - e.1 = (-1, 0)) :
    e = (((dualEdgeLeftCellCode e).1 + 1, (dualEdgeLeftCellCode e).2 + 1),
      ((dualEdgeLeftCellCode e).1, (dualEdgeLeftCellCode e).2 + 1)) ∧
      dualEdgeRightCellCode e = dualEdgeLeftCellCode e + (0, 1) := by
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := e
  change c - a = -1 at hx
  change d - b = 0 at hy
  have ha : a = c + 1 := by omega
  have hd : d = b := by omega
  subst a d
  rw [(dual_cells_of_left c b).1, (dual_cells_of_left c b).2]
  simp only [sub_add_cancel, Prod.mk_add_mk, add_zero, and_self]

private theorem down_edge_from_right {e : Lattice × Lattice} (h : e.2 - e.1 = (0, -1)) :
    e = (((dualEdgeRightCellCode e).1 + 1, (dualEdgeRightCellCode e).2 + 1),
      ((dualEdgeRightCellCode e).1 + 1, (dualEdgeRightCellCode e).2)) ∧
      dualEdgeLeftCellCode e = dualEdgeRightCellCode e + (1, 0) := by
  have hs : e.swap.2 - e.swap.1 = (0, 1) := by
    rw [Prod.snd_swap, Prod.fst_swap, ← neg_sub, h]
    rfl
  have he := up_edge_from_left hs
  exact ⟨congrArg Prod.swap he.1, he.2⟩

private theorem right_edge_from_right {e : Lattice × Lattice} (h : e.2 - e.1 = (1, 0)) :
    e = (((dualEdgeRightCellCode e).1, (dualEdgeRightCellCode e).2 + 1),
      ((dualEdgeRightCellCode e).1 + 1, (dualEdgeRightCellCode e).2 + 1)) ∧
      dualEdgeLeftCellCode e = dualEdgeRightCellCode e + (0, 1) := by
  have hs : e.swap.2 - e.swap.1 = (-1, 0) := by
    rw [Prod.snd_swap, Prod.fst_swap, ← neg_sub, h]
    rfl
  have he := left_edge_from_left hs
  exact ⟨congrArg Prod.swap he.1, he.2⟩

private theorem card_le_image_of_injOn {α β : Type} [DecidableEq β]
    {A B : Finset α} (hsub : A ⊆ B) {f : α → β} (hf : Set.InjOn f ↑A) :
    A.card ≤ (B.image f).card := by
  rw [← Finset.card_image_of_injOn hf]
  exact Finset.card_le_card (Finset.image_subset_image hsub)

/-- The distinct left cells of the upward and leftward sides number at least one fourth
of the circuit's length, and each has a forward neighbor outside. Final draft,  Lemma `lem:contour`, forward-label clause
and 2447. -/
theorem square_circuit_forward_cells {S : Finset Lattice} {m : ℕ}
    {v : Fin (m + 1) → Lattice} (hc : IsSquareCircuit v)
    (hsides : ∀ i, dualEdgeLeftCellCode (squareCircuitEdge v i) ∈ S ∧
      dualEdgeRightCellCode (squareCircuitEdge v i) ∉ S) :
    m ≤ 4 * (squareCircuitForwardCells hc).card ∧
      ∀ w ∈ squareCircuitForwardCells hc, w ∈ S ∧
        (w + (1, 0) ∉ S ∨ w + (0, 1) ∉ S) := by
  classical
  let A := Finset.univ.filter (fun i : Fin m =>
    v i.succ - v i.castSucc = (0, 1) ∨ v i.succ - v i.castSucc = (-1, 0))
  let U := Finset.univ.filter (fun i : Fin m => v i.succ - v i.castSucc = (0, 1))
  let L := Finset.univ.filter (fun i : Fin m => v i.succ - v i.castSucc = (-1, 0))
  let f := fun i => dualEdgeLeftCellCode (squareCircuitEdge v i)
  have hU : U ⊆ A := fun _ hi => Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, Or.inl (Finset.mem_filter.mp hi).2⟩
  have hL : L ⊆ A := fun _ hi => Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, Or.inr (Finset.mem_filter.mp hi).2⟩
  have hu : U.card ≤ (A.image f).card := card_le_image_of_injOn hU (by
    intro i hi j hj hEq
    apply hc.2.2.1
    have hi' := (up_edge_from_left (e := squareCircuitEdge v i) (Finset.mem_filter.mp hi).2).1
    have hj' := (up_edge_from_left (e := squareCircuitEdge v j) (Finset.mem_filter.mp hj).2).1
    change dualEdgeLeftCellCode (squareCircuitEdge v i) =
      dualEdgeLeftCellCode (squareCircuitEdge v j) at hEq
    rw [hi', hj', hEq])
  have hl : L.card ≤ (A.image f).card := card_le_image_of_injOn hL (by
    intro i hi j hj hEq
    apply hc.2.2.1
    have hi' := (left_edge_from_left (e := squareCircuitEdge v i) (Finset.mem_filter.mp hi).2).1
    have hj' := (left_edge_from_left (e := squareCircuitEdge v j) (Finset.mem_filter.mp hj).2).1
    change dualEdgeLeftCellCode (squareCircuitEdge v i) =
      dualEdgeLeftCellCode (squareCircuitEdge v j) at hEq
    rw [hi', hj', hEq])
  have hbalance : 2 * (U.card + L.card) = m :=
    (closed_lattice_walk_direction_balance m v hc.1 hc.2.1).2.2
  refine ⟨?_, ?_⟩
  · change m ≤ 4 * (A.image f).card
    omega
  · intro w hw
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
    refine ⟨(hsides i).1, ?_⟩
    rcases (Finset.mem_filter.mp hi).2 with hu | hl
    · exact Or.inl ((up_edge_from_left (e := squareCircuitEdge v i) hu).2 ▸ (hsides i).2)
    · exact Or.inr ((left_edge_from_left (e := squareCircuitEdge v i) hl).2 ▸ (hsides i).2)

/-- The distinct right cells of the downward and rightward sides number at least one fourth
of the circuit's length, and each has a forward neighbor inside. Final draft,  Lemma `lem:contour`, backward-label clause
and 2447. -/
theorem square_circuit_backward_cells {S : Finset Lattice} {m : ℕ}
    {v : Fin (m + 1) → Lattice} (hc : IsSquareCircuit v)
    (hsides : ∀ i, dualEdgeLeftCellCode (squareCircuitEdge v i) ∈ S ∧
      dualEdgeRightCellCode (squareCircuitEdge v i) ∉ S) :
    m ≤ 4 * (squareCircuitBackwardCells hc).card ∧
      ∀ w ∈ squareCircuitBackwardCells hc, w ∉ S ∧
        (w + (1, 0) ∈ S ∨ w + (0, 1) ∈ S) := by
  classical
  let A := Finset.univ.filter (fun i : Fin m =>
    v i.succ - v i.castSucc = (0, -1) ∨ v i.succ - v i.castSucc = (1, 0))
  let D := Finset.univ.filter (fun i : Fin m => v i.succ - v i.castSucc = (0, -1))
  let R := Finset.univ.filter (fun i : Fin m => v i.succ - v i.castSucc = (1, 0))
  let f := fun i => dualEdgeRightCellCode (squareCircuitEdge v i)
  have hD : D ⊆ A := fun _ hi => Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, Or.inl (Finset.mem_filter.mp hi).2⟩
  have hR : R ⊆ A := fun _ hi => Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, Or.inr (Finset.mem_filter.mp hi).2⟩
  have hd : D.card ≤ (A.image f).card := card_le_image_of_injOn hD (by
    intro i hi j hj hEq
    apply hc.2.2.1
    have hi' := (down_edge_from_right (e := squareCircuitEdge v i) (Finset.mem_filter.mp hi).2).1
    have hj' := (down_edge_from_right (e := squareCircuitEdge v j) (Finset.mem_filter.mp hj).2).1
    change dualEdgeRightCellCode (squareCircuitEdge v i) =
      dualEdgeRightCellCode (squareCircuitEdge v j) at hEq
    rw [hi', hj', hEq])
  have hr : R.card ≤ (A.image f).card := card_le_image_of_injOn hR (by
    intro i hi j hj hEq
    apply hc.2.2.1
    have hi' := (right_edge_from_right (e := squareCircuitEdge v i) (Finset.mem_filter.mp hi).2).1
    have hj' := (right_edge_from_right (e := squareCircuitEdge v j) (Finset.mem_filter.mp hj).2).1
    change dualEdgeRightCellCode (squareCircuitEdge v i) =
      dualEdgeRightCellCode (squareCircuitEdge v j) at hEq
    rw [hi', hj', hEq])
  have hbalance : 2 * (D.card + R.card) = m := by
    obtain ⟨hU, hL, htot⟩ := closed_lattice_walk_direction_balance m v hc.1 hc.2.1
    rw [hU, hL] at htot
    exact htot
  refine ⟨?_, ?_⟩
  · change m ≤ 4 * (A.image f).card
    omega
  · intro w hw
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
    refine ⟨(hsides i).2, ?_⟩
    rcases (Finset.mem_filter.mp hi).2 with hd | hr
    · exact Or.inl ((down_edge_from_right (e := squareCircuitEdge v i) hd).2 ▸ (hsides i).1)
    · exact Or.inr ((right_edge_from_right (e := squareCircuitEdge v i) hr).2 ▸ (hsides i).1)

private theorem cells_eq_of_cycle_eq {m : ℕ} {v w : Fin (m + 1) → Lattice}
    (hvw : squareCircuitCycle v = squareCircuitCycle w)
    (p : Lattice × Lattice → Prop) [DecidablePred p] (f : Lattice × Lattice → Lattice) :
    ((Finset.univ.filter (fun i => p (squareCircuitEdge v i))).image
      (fun i => f (squareCircuitEdge v i))) =
      ((Finset.univ.filter (fun i => p (squareCircuitEdge w i))).image
        (fun i => f (squareCircuitEdge w i))) := by
  have hsub {a b : Fin (m + 1) → Lattice} (hab : squareCircuitCycle a = squareCircuitCycle b) :
      ((Finset.univ.filter (fun i => p (squareCircuitEdge a i))).image
        (fun i => f (squareCircuitEdge a i))) ⊆
      ((Finset.univ.filter (fun i => p (squareCircuitEdge b i))).image
        (fun i => f (squareCircuitEdge b i))) := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    have he : squareCircuitEdge a i ∈ squareCircuitCycle a :=
      Cycle.mem_coe_iff.mpr (List.mem_ofFn.mpr ⟨i, rfl⟩)
    rw [hab] at he
    obtain ⟨j, hj⟩ := List.mem_ofFn.mp (Cycle.mem_coe_iff.mp he)
    exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hj.symm ▸ (Finset.mem_filter.mp hi).2⟩, congrArg f hj⟩
  exact Finset.Subset.antisymm (hsub hvw) (hsub hvw.symm)

/-- The circuit's forward cell set does not depend on the starting edge.
Final draft, Lemmas `lem:contour` and `lem:oriented`. -/
theorem square_circuit_forward_cells_eq_of_cycle_eq {m : ℕ} {v w : Fin (m + 1) → Lattice}
    (hv : IsSquareCircuit v) (hw : IsSquareCircuit w)
    (hvw : squareCircuitCycle v = squareCircuitCycle w) :
    squareCircuitForwardCells hv = squareCircuitForwardCells hw :=
  cells_eq_of_cycle_eq hvw
    (fun e => e.2 - e.1 = (0, 1) ∨ e.2 - e.1 = (-1, 0)) dualEdgeLeftCellCode

/-- The circuit's backward cell set does not depend on the starting edge.
Final draft, Lemma `lem:contour` and the staircase-geometry argument. -/
theorem square_circuit_backward_cells_eq_of_cycle_eq {m : ℕ} {v w : Fin (m + 1) → Lattice}
    (hv : IsSquareCircuit v) (hw : IsSquareCircuit w)
    (hvw : squareCircuitCycle v = squareCircuitCycle w) :
    squareCircuitBackwardCells hv = squareCircuitBackwardCells hw :=
  cells_eq_of_cycle_eq hvw
    (fun e => e.2 - e.1 = (0, -1) ∨ e.2 - e.1 = (1, 0)) dualEdgeRightCellCode

end LPPDifferentiability
