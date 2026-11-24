/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.FinalDraft.Contour.Definitions
public import LPP_Foundations.Model.Animals.Traversal
import Differentiability.FinalDraft.Contour.BoundarySelection
import Differentiability.FinalDraft.Contour.Count
import Differentiability.FinalDraft.Contour.Labels
import Differentiability.FinalDraft.Contour.RayGeometry

/-! The square contour lemma of the final differentiability draft. -/

public section

namespace LPPDifferentiability

/-- A finite nearest-neighbor connected set has a directed boundary circuit with the two
one-fourth label bounds, the area bound, and an edge among the first half-perimeter many
positive horizontal ray crossings. The number of possible circuits per length is at most
`m * 3 ^ (m - 1)`. Final draft, Lemma `lem:contour`. -/
theorem exists_square_contour (S : Finset Lattice) (hS : IsConnectedAnimal S)
    (z : Lattice) (hz : z ∈ S) :
    (∃ (m : ℕ) (v : Fin (m + 1) → Lattice) (hc : IsSquareCircuit v),
      4 ≤ m ∧
      (∀ i : Fin m, dualEdgeLeftCell ⟨squareCircuitEdge v i, hc.2.1 i⟩ ∈ S ∧
        dualEdgeRightCell ⟨squareCircuitEdge v i, hc.2.1 i⟩ ∉ S) ∧
      (m ≤ 4 * (squareCircuitForwardCells hc).card ∧
        ∀ w ∈ squareCircuitForwardCells hc, w ∈ S ∧
          (w + (1, 0) ∉ S ∨ w + (0, 1) ∉ S)) ∧
      (m ≤ 4 * (squareCircuitBackwardCells hc).card ∧
        ∀ w ∈ squareCircuitBackwardCells hc, w ∉ S ∧
          (w + (1, 0) ∈ S ∨ w + (0, 1) ∈ S)) ∧
      16 * S.card ≤ m ^ 2 ∧ SquareCircuitHitsRay z v) ∧
    (∀ m : ℕ, ∃ C : Finset (Cycle (Lattice × Lattice)),
      (∀ c, c ∈ C ↔ ∃ v : Fin (m + 1) → Lattice,
        IsSquareCircuit v ∧ SquareCircuitHitsRay z v ∧ squareCircuitCycle v = c) ∧
      C.card ≤ m * 3 ^ (m - 1)) := by
  refine ⟨?_, exists_finset_square_circuits_hitting_ray z⟩
  -- Cancel internal square sides and select a circuit from the Euler decomposition.
  obtain ⟨m, v, hc, hsides, hindex⟩ := exists_square_boundary_positive_index S z hz
  -- The selected circuit has positive ray index at every site in the connected set.
  have hpositive (w : Lattice) (hw : w ∈ S) : 0 < squareRayIndex v w := by
    rw [square_ray_index_eq_on_connected hS hc hsides hw hz]
    exact hindex
  -- Direction balance yields the label bounds and counts the occupied coordinate lines.
  obtain ⟨hm, harea⟩ := square_circuit_card_le hc ⟨z, hz⟩ hpositive
  exact ⟨m, v, hc, hm, hsides, square_circuit_forward_cells hc hsides,
    square_circuit_backward_cells hc hsides, harea, square_circuit_hits_ray hc z hindex⟩

end LPPDifferentiability
