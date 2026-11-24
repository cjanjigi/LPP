/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.FinalDraft.Contour.Definitions
public import LPP_Foundations.Model.Animals.Traversal
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-! The signed crossing sum of a horizontal ray for the final draft's contour proof.
The index is computed directly from the dual edges. -/

@[expose] public section

namespace LPPDifferentiability

/-- One edge's signed crossing of the east ray from a cell. Final draft, Appendix A contour edge-crossing definition. -/
def squareRayCrossing (z : Lattice) (e : Lattice × Lattice) : ℤ :=
  if e.1.2 = z.2 ∧ e.2.2 = z.2 + 1 ∧ z.1 + 1 ≤ e.1.1 then 1
  else if e.1.2 = z.2 + 1 ∧ e.2.2 = z.2 ∧ z.1 + 1 ≤ e.1.1 then -1 else 0

/-- The sum of the signed east-ray crossings in edge order. Final draft, Appendix A contour edge-crossing definition. -/
def squareRayIndex {m : ℕ} (v : Fin (m + 1) → Lattice) (z : Lattice) : ℤ :=
  ∑ i : Fin m, squareRayCrossing z (squareCircuitEdge v i)

private theorem sum_telescope_closed {m : ℕ} (v : Fin (m + 1) → Lattice)
    (hclosed : v 0 = v (Fin.last m)) (f : Lattice → ℤ) :
    ∑ i : Fin m, (f (v i.succ) - f (v i.castSucc)) = 0 := by
  have h₁ := Fin.sum_univ_succ (fun j : Fin (m + 1) => f (v j))
  have h₂ := Fin.sum_univ_castSucc (fun j : Fin (m + 1) => f (v j))
  rw [← hclosed] at h₂
  rw [Finset.sum_sub_distrib]
  omega

/-- The left and right cells for a up step. Final draft, Lemma `lem:contour`, side-cell definitions. -/
theorem dual_cells_of_up (a b : ℤ) :
    dualEdgeLeftCellCode ((a, b), (a, b + 1)) = (a - 1, b) ∧
      dualEdgeRightCellCode ((a, b), (a, b + 1)) = (a, b) := by
  simp [dualEdgeLeftCellCode, dualEdgeRightCellCode]

/-- The left and right cells for a right step. Final draft, Lemma `lem:contour`, side-cell definitions. -/
theorem dual_cells_of_right (a b : ℤ) :
    dualEdgeLeftCellCode ((a, b), (a + 1, b)) = (a, b) ∧
      dualEdgeRightCellCode ((a, b), (a + 1, b)) = (a, b - 1) := by
  simp [dualEdgeLeftCellCode, dualEdgeRightCellCode]

/-- The left and right cells for a down step. Final draft, Lemma `lem:contour`, side-cell definitions. -/
theorem dual_cells_of_down (a b : ℤ) :
    dualEdgeLeftCellCode ((a, b + 1), (a, b)) = (a, b) ∧
      dualEdgeRightCellCode ((a, b + 1), (a, b)) = (a - 1, b) := by
  exact ⟨(dual_cells_of_up a b).2, (dual_cells_of_up a b).1⟩

/-- The left and right cells for a left step. Final draft, Lemma `lem:contour`, side-cell definitions. -/
theorem dual_cells_of_left (a b : ℤ) :
    dualEdgeLeftCellCode ((a + 1, b), (a, b)) = (a, b - 1) ∧
      dualEdgeRightCellCode ((a + 1, b), (a, b)) = (a, b) := by
  exact ⟨(dual_cells_of_right a b).2, (dual_cells_of_right a b).1⟩

/-- Signed crossing counts are equal across a pair of horizontally neighboring cells when
their common side is unused. Final draft, Appendix A contour-side counting. -/
theorem square_ray_index_east_eq {m : ℕ} {v : Fin (m + 1) → Lattice}
    (hstep : ∀ i, IsDualUnitEdge (squareCircuitEdge v i)) (a b : ℤ)
    (hskip : ∀ i, squareCircuitEdge v i ≠ ((a + 1, b), (a + 1, b + 1)) ∧
      squareCircuitEdge v i ≠ ((a + 1, b + 1), (a + 1, b))) :
    squareRayIndex v (a, b) = squareRayIndex v (a + 1, b) := by
  unfold squareRayIndex
  apply Finset.sum_congr rfl
  intro i _
  let c := v i.castSucc
  let s := v i.succ
  have hcoord := dual_unit_edge_cases (show IsDualUnitEdge (c, s) from hstep i)
  have h₁ : ¬ (c = (a + 1, b) ∧ s = (a + 1, b + 1)) :=
    fun ⟨hc, hs⟩ => (hskip i).1 (Prod.ext hc hs)
  have h₂ : ¬ (c = (a + 1, b + 1) ∧ s = (a + 1, b)) :=
    fun ⟨hc, hs⟩ => (hskip i).2 (Prod.ext hc hs)
  change squareRayCrossing (a, b) (c, s) = squareRayCrossing (a + 1, b) (c, s)
  simp only [Prod.ext_iff] at h₁ h₂
  simp only [squareRayCrossing]
  split_ifs <;> omega

/-- Signed crossing counts are equal across a pair of vertically neighboring cells when
their common side is unused. Final draft, Appendix A contour-side counting. -/
theorem square_ray_index_north_eq {m : ℕ} {v : Fin (m + 1) → Lattice}
    (hclosed : v 0 = v (Fin.last m))
    (hstep : ∀ i, IsDualUnitEdge (squareCircuitEdge v i)) (a b : ℤ)
    (hskip : ∀ i, squareCircuitEdge v i ≠ ((a, b + 1), (a + 1, b + 1)) ∧
      squareCircuitEdge v i ≠ ((a + 1, b + 1), (a, b + 1))) :
    squareRayIndex v (a, b) = squareRayIndex v (a, b + 1) := by
  apply sub_eq_zero.mp
  rw [squareRayIndex, squareRayIndex, ← Finset.sum_sub_distrib]
  let f : Lattice → ℤ := fun u => if u.2 = b + 1 ∧ a + 1 ≤ u.1 then 1 else 0
  rw [← sum_telescope_closed v hclosed f]
  apply Finset.sum_congr rfl
  intro i _
  let c := v i.castSucc
  let s := v i.succ
  have hcoord := dual_unit_edge_cases (show IsDualUnitEdge (c, s) from hstep i)
  have h₁ : ¬ (c = (a, b + 1) ∧ s = (a + 1, b + 1)) :=
    fun ⟨hc, hs⟩ => (hskip i).1 (Prod.ext hc hs)
  have h₂ : ¬ (c = (a + 1, b + 1) ∧ s = (a, b + 1)) :=
    fun ⟨hc, hs⟩ => (hskip i).2 (Prod.ext hc hs)
  change squareRayCrossing (a, b) (c, s) - squareRayCrossing (a, b + 1) (c, s) = f s - f c
  simp only [Prod.ext_iff] at h₁ h₂
  simp only [squareRayCrossing, f]
  split_ifs <;> omega

/-- The index is constant on the finite connected set whose cells lie on the left of the
circuit. Final draft, Appendix A contour-side counting. -/
theorem square_ray_index_eq_on_connected {S : Finset Lattice} (hS : IsConnectedAnimal S)
    {m : ℕ} {v : Fin (m + 1) → Lattice} (hc : IsSquareCircuit v)
    (hsides : ∀ i, dualEdgeLeftCellCode (squareCircuitEdge v i) ∈ S ∧
      dualEdgeRightCellCode (squareCircuitEdge v i) ∉ S)
    {x y : Lattice} (hx : x ∈ S) (hy : y ∈ S) :
    squareRayIndex v x = squareRayIndex v y := by
  have hEast (a b : ℤ) (h₀ : (a, b) ∈ S) (h₁ : (a + 1, b) ∈ S) :
      squareRayIndex v (a, b) = squareRayIndex v (a + 1, b) := by
    apply square_ray_index_east_eq hc.2.1
    intro i
    constructor
    · intro he
      exact (hsides i).2 (he.symm ▸ (dual_cells_of_up (a + 1) b).2.symm ▸ h₁)
    · intro he
      have hd := (hsides i).2
      rw [he, (dual_cells_of_down (a + 1) b).2, add_sub_cancel_right] at hd
      exact hd h₀
  have hNorth (a b : ℤ) (h₀ : (a, b) ∈ S) (h₁ : (a, b + 1) ∈ S) :
      squareRayIndex v (a, b) = squareRayIndex v (a, b + 1) := by
    apply square_ray_index_north_eq hc.1 hc.2.1
    intro i
    constructor
    · intro he
      have hr := (hsides i).2
      rw [he, (dual_cells_of_right a (b + 1)).2, add_sub_cancel_right] at hr
      exact hr h₀
    · intro he
      exact (hsides i).2 (he.symm ▸ (dual_cells_of_left a (b + 1)).2.symm ▸ h₁)
  let G := nearestNeighborGraph.induce (↑S : Set Lattice)
  have hAdj (p q : ↑(↑S : Set Lattice)) (hpq : G.Adj p q) :
      squareRayIndex v p.val = squareRayIndex v q.val := by
    have hp : p.val ∈ S := p.property
    have hq : q.val ∈ S := q.property
    change (|p.val.1 - q.val.1| = 1 ∧ p.val.2 = q.val.2) ∨
      (p.val.1 = q.val.1 ∧ |p.val.2 - q.val.2| = 1) at hpq
    rcases hpq with ⟨habs, hy⟩ | ⟨hx, habs⟩
    · rcases (show q.val.1 = p.val.1 + 1 ∨ p.val.1 = q.val.1 + 1 from by
            simp only [abs_eq_max_neg] at habs
            omega) with h | h
      · have he : q.val = (p.val.1 + 1, p.val.2) := Prod.ext h hy.symm
        rw [he] at hq ⊢
        exact hEast _ _ hp hq
      · have he : p.val = (q.val.1 + 1, q.val.2) := Prod.ext h hy
        rw [he] at hp ⊢
        exact (hEast _ _ hq hp).symm
    · rcases (show q.val.2 = p.val.2 + 1 ∨ p.val.2 = q.val.2 + 1 from by
          simp only [abs_eq_max_neg] at habs
          omega) with h | h
      · have he : q.val = (p.val.1, p.val.2 + 1) := Prod.ext hx.symm h
        rw [he] at hq ⊢
        exact hNorth _ _ hp hq
      · have he : p.val = (q.val.1, q.val.2 + 1) := Prod.ext hx h
        rw [he] at hp ⊢
        exact (hNorth _ _ hq hp).symm
  have onWalk {p q : ↑(↑S : Set Lattice)} (w : G.Walk p q) :
      squareRayIndex v p.val = squareRayIndex v q.val := by
    induction w with
    | nil => rfl
    | cons hadj _ ih => exact (hAdj _ _ hadj).trans ih
  obtain ⟨w⟩ := hS.preconnected ⟨x, hx⟩ ⟨y, hy⟩
  exact onWalk w

end LPPDifferentiability
