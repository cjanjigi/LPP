/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.Lattice
public import Mathlib.Data.List.Cycle
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Fintype.Basic
import Lean.Elab.Tactic.Omega

/-! The dual circuits and their adjacent primal cells in the final differentiability draft.
A dual vertex with integer code `v` is at `v - (1/2, 1/2)` in the plane. -/

@[expose] public section

namespace LPPDifferentiability

/-- The directed edge from vertex `i` to its successor. Final draft, Lemma `lem:contour`. -/
def squareCircuitEdge {m : ℕ} (v : Fin (m + 1) → Lattice) (i : Fin m) :
    Lattice × Lattice :=
  (v i.castSucc, v i.succ)

/-- A dual unit edge connects nearest-neighbor corner codes. Final draft, Lemma `lem:contour`. -/
def IsDualUnitEdge (e : Lattice × Lattice) : Prop :=
  e.2 - e.1 = (0, 1) ∨ e.2 - e.1 = (0, -1) ∨
    e.2 - e.1 = (-1, 0) ∨ e.2 - e.1 = (1, 0)

/-- A circuit is a closed unit walk with each unoriented edge used at most once.
Final draft, Lemma `lem:contour`. -/
def IsSquareCircuit {m : ℕ} (v : Fin (m + 1) → Lattice) : Prop :=
  v 0 = v (Fin.last m) ∧
    (∀ i, IsDualUnitEdge (squareCircuitEdge v i)) ∧
    Function.Injective (squareCircuitEdge v) ∧
    ∀ i j, (squareCircuitEdge v i).swap ≠ squareCircuitEdge v j

/-- Edge order with no distinguished starting edge. Reversing orientation still changes each
edge. Final draft, Lemmas `lem:contour` and `lem:oriented`. -/
def squareCircuitCycle {m : ℕ} (v : Fin (m + 1) → Lattice) :
    Cycle (Lattice × Lattice) :=
  ↑(List.ofFn (squareCircuitEdge v))

/-- Coordinate calculation used for the left cell of a unit edge. -/
def dualEdgeLeftCellCode (e : Lattice × Lattice) : Lattice :=
  (min e.1.1 e.2.1 - (if e.1.2 < e.2.2 then 1 else 0),
   min e.1.2 e.2.2 - (if e.2.1 < e.1.1 then 1 else 0))

/-- Coordinate calculation used for the right cell of a unit edge. -/
def dualEdgeRightCellCode (e : Lattice × Lattice) : Lattice :=
  dualEdgeLeftCellCode e.swap

/-- A directed nearest-neighbor edge of the dual lattice. Final draft, Lemma `lem:contour`. -/
abbrev DualUnitEdge := {e : Lattice × Lattice // IsDualUnitEdge e}

/-- The primal cell on the left of a directed dual unit edge. Final draft, Lemma `lem:contour`. -/
def dualEdgeLeftCell (e : DualUnitEdge) : Lattice :=
  dualEdgeLeftCellCode e.val

/-- The primal cell on the right of a directed dual unit edge. Final draft, Lemma `lem:contour`. -/
def dualEdgeRightCell (e : DualUnitEdge) : Lattice :=
  dualEdgeRightCellCode e.val

/-- The distinct left cells of upward and leftward edges. Final draft, Lemma `lem:contour`, forward-label bound. -/
def squareCircuitForwardCells {m : ℕ} {v : Fin (m + 1) → Lattice}
    (hc : IsSquareCircuit v) : Finset Lattice :=
  (Finset.univ.filter (fun i : Fin m =>
    v i.succ - v i.castSucc = (0, 1) ∨ v i.succ - v i.castSucc = (-1, 0))).image
    (fun i => dualEdgeLeftCell ⟨squareCircuitEdge v i, hc.2.1 i⟩)

/-- The distinct right cells of downward and rightward edges. Final draft, Lemma `lem:contour`, backward-label bound. -/
def squareCircuitBackwardCells {m : ℕ} {v : Fin (m + 1) → Lattice}
    (hc : IsSquareCircuit v) : Finset Lattice :=
  (Finset.univ.filter (fun i : Fin m =>
    v i.succ - v i.castSucc = (0, -1) ∨ v i.succ - v i.castSucc = (1, 0))).image
    (fun i => dualEdgeRightCell ⟨squareCircuitEdge v i, hc.2.1 i⟩)

/-- The common side of the cells at `z + (j-1)e₁` and `z + je₁`, oriented upward.
Final draft, Lemma `lem:contour`, perimeter count. -/
def squareCircuitRayEdge (z : Lattice) (j : ℕ) : Lattice × Lattice :=
  ((z.1 + j, z.2), (z.1 + j, z.2 + 1))

/-- A circuit contains an unoriented edge among the first `m / 2` positive ray edges.
Final draft, Lemma `lem:contour`, perimeter count. -/
def SquareCircuitHitsRay (z : Lattice) {m : ℕ} (v : Fin (m + 1) → Lattice) : Prop :=
  ∃ j : ℕ, 1 ≤ j ∧ j ≤ m / 2 ∧ ∃ i : Fin m,
    squareCircuitEdge v i = squareCircuitRayEdge z j ∨
    squareCircuitEdge v i = (squareCircuitRayEdge z j).swap

/-- The four unit directions as coordinate equations. Final draft, Lemma `lem:contour`. -/
theorem dual_unit_edge_cases {c s : Lattice} (h : IsDualUnitEdge (c, s)) :
    (s.1 = c.1 ∧ s.2 = c.2 + 1) ∨ (s.1 = c.1 ∧ s.2 = c.2 - 1) ∨
    (s.1 = c.1 - 1 ∧ s.2 = c.2) ∨ (s.1 = c.1 + 1 ∧ s.2 = c.2) := by
  rcases h with he | he | he | he
  all_goals
    have hx := congrArg Prod.fst he
    have hy := congrArg Prod.snd he
    simp only [Prod.fst_sub, Prod.snd_sub] at hx hy
    omega

end LPPDifferentiability
