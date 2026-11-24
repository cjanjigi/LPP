/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen
-/
module

public import Differentiability.FinalDraft.Contour.Definitions
import Differentiability.FinalDraft.Contour.Count
import Differentiability.FinalDraft.Contour.Existence
import Differentiability.Model.FiniteOrientedCluster
import Differentiability.Model.OrientedEndpointClosure
import Mathlib.Tactic

/-! The endpoint cluster gives a square contour with bad forward labels. -/

public section

namespace LPPDifferentiability

private abbrev Site := ℕ × ℕ

private def castSite (x : Site) : Lattice := ((x.1 : ℤ), (x.2 : ℤ))

private def naturalSite (w : Lattice) : Site := (w.1.toNat, w.2.toNat)

private theorem naturalSite_castSite (x : Site) : naturalSite (castSite x) = x := by
  simp [naturalSite, castSite]

private theorem castSite_add (x y : Site) : castSite (x + y) = castSite x + castSite y := by
  apply Prod.ext <;> simp only [castSite, Prod.fst_add, Prod.snd_add, Nat.cast_add]

private def endpointCluster (G : Set Site) : Set Site :=
  {x | ∃ n : ℕ, ∃ q : Fin (n + 1) → Site,
    q 0 = (0, 0) ∧ q (Fin.last n) = x ∧
    (∀ i : Fin n, q i.succ = q i.castSucc + (1, 0) ∨ q i.succ = q i.castSucc + (0, 1)) ∧
    ∀ i : Fin (n + 1), (i : ℕ) < n → q i ∈ G}

private theorem oriented_vertex_mem_cluster {G : Set Site} {n : ℕ}
    (q : Fin (n + 1) → Site) (hzero : q 0 = (0, 0))
    (hstep : ∀ i : Fin n, q i.succ = q i.castSucc + (1, 0) ∨
      q i.succ = q i.castSucc + (0, 1))
    (hgood : ∀ i : Fin (n + 1), i.val < n → q i ∈ G) (j : Fin (n + 1)) :
    q j ∈ endpointCluster G := by
  let p (i : Fin (j.val + 1)) : Site := q ⟨i.val, by have := j.isLt; omega⟩
  refine ⟨j.val, p, hzero, ?_, ?_, ?_⟩
  · change q ⟨j.val, j.isLt⟩ = q j
    rfl
  · intro i
    exact hstep ⟨i.val, by have := i.isLt; have := j.isLt; omega⟩
  · intro i hi
    exact hgood ⟨i.val, by have := j.isLt; omega⟩
      (Nat.lt_of_lt_of_le hi (Nat.le_of_lt_succ j.isLt))

private theorem castSite_step_adj {x y : Site} (h : y = x + (1, 0) ∨ y = x + (0, 1)) :
    nearestNeighborGraph.Adj (castSite x) (castSite y) := by
  rcases h with rfl | rfl
  · left
    simp [castSite, show (x.1 : ℤ) - ((x.1 : ℤ) + 1) = -1 by omega]
  · right
    simp [castSite, show (x.2 : ℤ) - ((x.2 : ℤ) + 1) = -1 by omega]

private theorem endpoint_cluster_connected {G : Set Site} {S : Finset Site}
    (hS : ∀ x, x ∈ S ↔ x ∈ endpointCluster G) :
    IsConnectedAnimal (S.image castSite) := by
  classical
  let T := S.image castSite
  have hz : (0 : Lattice) ∈ (T : Set Lattice) :=
    Finset.mem_image.mpr ⟨(0, 0), (hS _).mpr (oriented_endpoint_set_zero G), rfl⟩
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).2
  refine ⟨⟨0, hz⟩, ?_⟩
  intro ⟨y, hy⟩
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
  obtain ⟨n, q, hzero, hlast, hstep, hgood⟩ := (hS x).mp hx
  have hvertices (j : Fin (n + 1)) : castSite (q j) ∈ (T : Set Lattice) :=
    Finset.mem_image.mpr ⟨q j, (hS _).mpr (oriented_vertex_mem_cluster q hzero hstep hgood j), rfl⟩
  have hreach (j : ℕ) (hj : j ≤ n) :
      (nearestNeighborGraph.induce (T : Set Lattice)).Reachable
        ⟨castSite (q 0), hvertices 0⟩
        ⟨castSite (q ⟨j, by omega⟩), hvertices ⟨j, by omega⟩⟩ := by
    induction j with
    | zero => exact SimpleGraph.Reachable.rfl
    | succ j ih =>
      apply (ih (by omega)).trans
      apply SimpleGraph.Adj.reachable
      exact castSite_step_adj (hstep ⟨j, by omega⟩)
  have hpath := hreach n le_rfl
  have h0 : (⟨castSite (q 0), hvertices 0⟩ : (T : Set Lattice)) = ⟨0, hz⟩ :=
    Subtype.ext (congrArg castSite hzero)
  have h1 : (⟨castSite (q (Fin.last n)), hvertices (Fin.last n)⟩ : (T : Set Lattice)) =
      ⟨castSite x, hy⟩ := Subtype.ext (congrArg castSite hlast)
  rw [h0] at hpath
  exact h1 ▸ hpath

private def cycleForwardCells (c : Cycle (Lattice × Lattice)) : Finset Lattice :=
  (c.toFinset.filter (fun e => e.2 - e.1 = (0, 1) ∨ e.2 - e.1 = (-1, 0))).image
    dualEdgeLeftCellCode

private theorem cycleForwardCells_eq {m : ℕ} {v : Fin (m + 1) → Lattice}
    (hc : IsSquareCircuit v) :
    cycleForwardCells (squareCircuitCycle v) = squareCircuitForwardCells hc := by
  ext w
  simp only [cycleForwardCells, squareCircuitCycle, Cycle.coe_toFinset,
    squareCircuitForwardCells, Finset.mem_image, Finset.mem_filter, List.mem_toFinset,
    List.mem_ofFn, Finset.mem_univ, true_and, squareCircuitEdge, dualEdgeLeftCell]
  aesop

/-- The forward labels of a circuit in the natural quadrant, as in the proof of
Lemma `lem:oriented` in the final draft. The label set is independent of the good sites. -/
def squareContourForwardSites (c : Cycle (Lattice × Lattice)) : Finset (ℕ × ℕ) :=
  ((cycleForwardCells c).filter (fun w => 0 ≤ w.1 ∧ 0 ≤ w.2)).image naturalSite

private theorem good_cluster_forward_cell_is_bad (G : Set Site) (S : Finset Site)
    (hS : ∀ x, x ∈ S ↔ x ∈ endpointCluster G) {w : Lattice}
    (hw : w ∈ S.image castSite)
    (hexit : w + (1, 0) ∉ S.image castSite ∨ w + (0, 1) ∉ S.image castSite) :
    naturalSite w ∉ G := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hw
  rw [naturalSite_castSite]
  apply oriented_endpoint_set_bad_of_forward_exit G x ((hS x).mp hx)
  rcases hexit with h | h
  · left
    intro hmem
    apply h
    exact Finset.mem_image.mpr ⟨x + (1, 0), (hS _).mpr hmem, castSite_add x (1, 0)⟩
  · right
    intro hmem
    apply h
    exact Finset.mem_image.mpr ⟨x + (0, 1), (hS _).mpr hmem, castSite_add x (0, 1)⟩

private theorem exists_bad_forward_square_contour (G : Set Site)
    (hno : ¬ ∃ v : ℕ → Site, v 0 = (0, 0) ∧
      (∀ i, v (i + 1) = v i + (1, 0) ∨ v (i + 1) = v i + (0, 1)) ∧ ∀ i, v i ∈ G) :
    ∃ (m : ℕ) (v : Fin (m + 1) → Lattice),
      4 ≤ m ∧ IsSquareCircuit v ∧ SquareCircuitHitsRay 0 v ∧
      m ≤ 4 * (squareContourForwardSites (squareCircuitCycle v)).card ∧
      ∀ x ∈ squareContourForwardSites (squareCircuitCycle v), x ∉ G := by
  classical
  have hfinite := finite_oriented_endpoint_set G hno
  let S := hfinite.toFinset
  have hS (x : Site) : x ∈ S ↔ x ∈ endpointCluster G := hfinite.mem_toFinset
  let T := S.image castSite
  have hzero : (0 : Lattice) ∈ T :=
    Finset.mem_image.mpr ⟨(0, 0), (hS _).mpr (oriented_endpoint_set_zero G), rfl⟩
  -- Take the contour of the actual finite endpoint cluster, including possible bad endpoints.
  obtain ⟨m, v, hc, hm, _, ⟨hcount, hlabels⟩, _, _, hray⟩ :=
    (exists_square_contour T (endpoint_cluster_connected hS) 0 hzero).1
  have hcast (w : Lattice) (hw : w ∈ squareCircuitForwardCells hc) :
      ∃ x ∈ S, castSite x = w := Finset.mem_image.mp (hlabels w hw).1
  have hquad (w : Lattice) (hw : w ∈ squareCircuitForwardCells hc) :
      0 ≤ w.1 ∧ 0 ≤ w.2 := by
    obtain ⟨x, _, rfl⟩ := hcast w hw
    exact ⟨Int.natCast_nonneg _, Int.natCast_nonneg _⟩
  have hsites : squareContourForwardSites (squareCircuitCycle v) =
      (squareCircuitForwardCells hc).image naturalSite := by
    rw [squareContourForwardSites, cycleForwardCells_eq hc, Finset.filter_eq_self.mpr hquad]
  refine ⟨m, v, hm, hc, hray, ?_, ?_⟩
  · rw [hsites, Finset.card_image_of_injOn]
    · exact hcount
    · intro a ha b hb hab
      obtain ⟨x, _, rfl⟩ := hcast a ha
      obtain ⟨y, _, rfl⟩ := hcast b hb
      rw [naturalSite_castSite, naturalSite_castSite] at hab
      exact congrArg castSite hab
  · rw [hsites]
    intro x hx
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
    exact good_cluster_forward_cell_is_bad G S hS (hlabels w hw).1 (hlabels w hw).2

/-- A deterministic family of at most `m * 3^(m-1)` circuits covers each length `m = n+4`.
Failure of the infinite-path event forces every forward label of a counted circuit to
be bad. Final draft, proof of Lemma `lem:oriented`. -/
theorem exists_square_contour_bad_site_cover :
    ∃ C : ℕ → Finset (Cycle (Lattice × Lattice)),
      (∀ n, (C n).card ≤ (n + 4) * 3 ^ (n + 3)) ∧
      (∀ n c, c ∈ C n → n + 4 ≤ 4 * (squareContourForwardSites c).card) ∧
      ∀ G : Set (ℕ × ℕ),
        (¬ ∃ q : ℕ → ℕ × ℕ, q 0 = (0, 0) ∧
          (∀ i, q (i + 1) = q i + (1, 0) ∨ q (i + 1) = q i + (0, 1)) ∧
          ∀ i, q i ∈ G) →
        ∃ n c, c ∈ C n ∧ ∀ x ∈ squareContourForwardSites c, x ∉ G := by
  classical
  choose C hC hCount using exists_finset_square_circuits_hitting_ray (0 : Lattice)
  let D (n : ℕ) := (C (n + 4)).filter fun c => n + 4 ≤ 4 * (squareContourForwardSites c).card
  refine ⟨D, ?_, fun n c hc => (Finset.mem_filter.mp hc).2, ?_⟩
  · intro n
    exact (Finset.card_filter_le _ _).trans
      (by simpa only [show n + 4 - 1 = n + 3 by omega] using hCount (n + 4))
  · intro G hno
    obtain ⟨m, v, hm, hc, hray, hcard, hbad⟩ := exists_bad_forward_square_contour G hno
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n + 4 := ⟨m - 4, by omega⟩
    exact ⟨n, squareCircuitCycle v,
      Finset.mem_filter.mpr ⟨(hC _ _).mpr ⟨v, hc, hray, rfl⟩, hcard⟩, hbad⟩

end LPPDifferentiability
