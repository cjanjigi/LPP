/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.FinalDraft.Contour.BoundaryIndex
import Differentiability.Model.SquareBoundaryBalance
import Differentiability.Model.FiniteDirectedCircuitDecomposition
import Mathlib.Tactic

/-! Select a circuit in the Euler decomposition by additivity of the signed east-ray sum. -/

public section

namespace LPPDifferentiability

private abbrev IsSquareBoundary (S : Finset Lattice)
    (E : Finset (Lattice × Lattice)) : Prop :=
  ∀ e, e ∈ E ↔ ∃ w, w ∈ S ∧
    ((e = ((w.1, w.2), (w.1 + 1, w.2)) ∧ (w.1, w.2 - 1) ∉ S) ∨
     (e = ((w.1 + 1, w.2), (w.1 + 1, w.2 + 1)) ∧ (w.1 + 1, w.2) ∉ S) ∨
     (e = ((w.1 + 1, w.2 + 1), (w.1, w.2 + 1)) ∧ (w.1, w.2 + 1) ∉ S) ∨
     (e = ((w.1, w.2 + 1), (w.1, w.2)) ∧ (w.1 - 1, w.2) ∉ S))

private theorem boundary_sides {S : Finset Lattice} {E : Finset (Lattice × Lattice)}
    (hmem : IsSquareBoundary S E) {e : Lattice × Lattice} (he : e ∈ E) :
    dualEdgeLeftCellCode e ∈ S ∧ dualEdgeRightCellCode e ∉ S := by
  obtain ⟨w, hw, hs⟩ := (hmem e).mp he
  rcases hs with ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn⟩
  · simpa only [(dual_cells_of_right w.1 w.2).1, (dual_cells_of_right w.1 w.2).2]
      using And.intro hw hn
  · simpa only [(dual_cells_of_up (w.1 + 1) w.2).1, (dual_cells_of_up (w.1 + 1) w.2).2,
      add_sub_cancel_right] using And.intro hw hn
  · simpa only [(dual_cells_of_left w.1 (w.2 + 1)).1, (dual_cells_of_left w.1 (w.2 + 1)).2,
      add_sub_cancel_right] using And.intro hw hn
  · simpa only [(dual_cells_of_down w.1 w.2).1, (dual_cells_of_down w.1 w.2).2]
      using And.intro hw hn

private theorem boundary_up_mem_iff {S : Finset Lattice} {E : Finset (Lattice × Lattice)}
    (hmem : IsSquareBoundary S E) (a b : ℤ) :
    ((a, b), (a, b + 1)) ∈ E ↔ (a - 1, b) ∈ S ∧ (a, b) ∉ S := by
  constructor
  · intro he
    have hs := boundary_sides hmem he
    rwa [(dual_cells_of_up a b).1, (dual_cells_of_up a b).2] at hs
  · rintro ⟨hw, hn⟩
    exact (hmem _).mpr ⟨(a - 1, b), hw, Or.inr (Or.inl
      ⟨by simp only [sub_add_cancel], by simpa only [sub_add_cancel] using hn⟩)⟩

private theorem boundary_down_mem_iff {S : Finset Lattice} {E : Finset (Lattice × Lattice)}
    (hmem : IsSquareBoundary S E) (a b : ℤ) :
    ((a, b + 1), (a, b)) ∈ E ↔ (a, b) ∈ S ∧ (a - 1, b) ∉ S := by
  constructor
  · intro he
    have hs := boundary_sides hmem he
    rwa [(dual_cells_of_down a b).1, (dual_cells_of_down a b).2] at hs
  · rintro ⟨hw, hn⟩
    exact (hmem _).mpr ⟨(a, b), hw, Or.inr (Or.inr (Or.inr ⟨rfl, hn⟩))⟩

private theorem boundary_unit {S : Finset Lattice} {E : Finset (Lattice × Lattice)}
    (hmem : IsSquareBoundary S E) {e : Lattice × Lattice} (he : e ∈ E) :
    IsDualUnitEdge e := by
  obtain ⟨⟨a, b⟩, _, hs⟩ := (hmem e).mp he
  have hx : a - (a + 1) = -1 := by omega
  have hy : b - (b + 1) = -1 := by omega
  rcases hs with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
  · simp [IsDualUnitEdge]
  · simp [IsDualUnitEdge]
  · simp [IsDualUnitEdge, hx]
  · simp [IsDualUnitEdge, hy]

private theorem square_boundary_ray_sum {S : Finset Lattice} {E : Finset (Lattice × Lattice)}
    (hmem : IsSquareBoundary S E) {z : Lattice} (hz : z ∈ S) :
    ∑ e ∈ E, squareRayCrossing z e = 1 := by
  classical
  let K : ℕ := ∑ w ∈ S, w.1.natAbs
  have hK (w : Lattice) (hw : w ∈ S) : w.1 ≤ (K : ℤ) := by
    have hk : w.1.natAbs ≤ K := Finset.single_le_sum
      (f := fun x : Lattice => x.1.natAbs) (fun _ _ => Nat.zero_le _) hw
    have hk' : (w.1.natAbs : ℤ) ≤ K := by exact_mod_cast hk
    exact Int.le_natAbs.trans hk'
  let n := ((K : ℤ) - z.1 + 1).toNat
  have hn : (n : ℤ) = (K : ℤ) - z.1 + 1 := by
    apply Int.toNat_of_nonneg
    have := hK z hz
    omega
  let up (k : ℕ) : Lattice × Lattice := ((z.1 + k + 1, z.2), (z.1 + k + 1, z.2 + 1))
  let down (k : ℕ) : Lattice × Lattice := ((z.1 + k + 1, z.2 + 1), (z.1 + k + 1, z.2))
  let U := (Finset.range n).image up
  let D := (Finset.range n).image down
  let X := U ∪ D
  have hX (e : Lattice × Lattice) (he : e ∈ E) (hcross : squareRayCrossing z e ≠ 0) : e ∈ X := by
    have hcoord := dual_unit_edge_cases (boundary_unit hmem he)
    have hmax : e.1.1 ≤ (K : ℤ) + 1 := by
      obtain ⟨w, hw, hs⟩ := (hmem e).mp he
      have := hK w hw
      rcases hs with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp only <;> omega
    have hx : z.1 + 1 ≤ e.1.1 := by
      unfold squareRayCrossing at hcross
      split_ifs at hcross with h₁ h₂
      · exact h₁.2.2
      · exact h₂.2.2
      · exact (hcross rfl).elim
    let k := (e.1.1 - z.1 - 1).toNat
    have hk : (k : ℤ) = e.1.1 - z.1 - 1 := Int.toNat_of_nonneg (by omega)
    have hkn : k ∈ Finset.range n := Finset.mem_range.mpr (by omega)
    unfold squareRayCrossing at hcross
    split_ifs at hcross with h₁ h₂
    · apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨k, hkn, Prod.ext (Prod.ext (by dsimp [up]; omega) h₁.1.symm)
        (Prod.ext (by dsimp [up]; omega) h₁.2.1.symm)⟩
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨k, hkn, Prod.ext (Prod.ext (by dsimp [down]; omega) h₂.1.symm)
        (Prod.ext (by dsimp [down]; omega) h₂.2.1.symm)⟩
    · exact (hcross rfl).elim
  have hdisj : Disjoint U D := by
    apply Finset.disjoint_left.mpr
    intro e hu hd
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨l, _, h⟩ := Finset.mem_image.mp hd
    have hy := congrArg (fun e : Lattice × Lattice => e.1.2) h
    dsimp [down, up] at hy
    omega
  have hu : Set.InjOn up ↑(Finset.range n) := by
    intro k _ l _ h
    have hx := congrArg (fun e : Lattice × Lattice => e.1.1) h
    dsimp [up] at hx
    omega
  have hd : Set.InjOn down ↑(Finset.range n) := by
    intro k _ l _ h
    have hx := congrArg (fun e : Lattice × Lattice => e.1.1) h
    dsimp [down] at hx
    omega
  let F (e : Lattice × Lattice) : ℤ := if e ∈ E then squareRayCrossing z e else 0
  have hreindex : ∑ e ∈ E, squareRayCrossing z e = ∑ e ∈ X, F e := by
    rw [← Finset.sum_filter]
    change ∑ e ∈ E, squareRayCrossing z e = ∑ e ∈ X.filter (· ∈ E), squareRayCrossing z e
    symm
    apply Finset.sum_subset
    · exact fun e he => (Finset.mem_filter.mp he).2
    · intro e he hne
      by_contra hc
      exact hne (Finset.mem_filter.mpr ⟨hX e he hc, he⟩)
  let f (k : ℕ) : ℤ := if (z.1 + k, z.2) ∈ S then 1 else 0
  have hterm (k : ℕ) : F (up k) + F (down k) = f k - f (k + 1) := by
    have hu := boundary_up_mem_iff hmem (z.1 + k + 1) z.2
    have hd := boundary_down_mem_iff hmem (z.1 + k + 1) z.2
    have hx : z.1 + 1 ≤ z.1 + (k : ℤ) + 1 := by omega
    have hne : z.2 + 1 ≠ z.2 := by omega
    have hcrossU : squareRayCrossing z (up k) = 1 := by
      simp [up, squareRayCrossing, hx]
    have hcrossD : squareRayCrossing z (down k) = -1 := by
      simp [down, squareRayCrossing, hx, hne]
    have hu' : up k ∈ E ↔ (z.1 + k, z.2) ∈ S ∧ (z.1 + (k + 1 : ℕ), z.2) ∉ S := by
      simpa only [up, add_sub_cancel_right, Nat.cast_succ, ← add_assoc] using hu
    have hd' : down k ∈ E ↔ (z.1 + (k + 1 : ℕ), z.2) ∈ S ∧ (z.1 + k, z.2) ∉ S := by
      simpa only [down, add_sub_cancel_right, Nat.cast_succ, ← add_assoc] using hd
    simp only [F, hcrossU, hcrossD, hu', hd', f, Nat.cast_succ]
    by_cases hleft : (z.1 + k, z.2) ∈ S <;>
      by_cases hright : (z.1 + ((k : ℤ) + 1), z.2) ∈ S <;>
      simp [hleft, hright]
  have hf0 : f 0 = 1 := by simpa [f] using hz
  have hfn : f n = 0 := by
    have hnot : (z.1 + n, z.2) ∉ S := by
      intro hw
      have := hK _ hw
      dsimp only at this
      omega
    simp only [f, hnot, ite_false]
  rw [hreindex, Finset.sum_union hdisj, Finset.sum_image hu, Finset.sum_image hd,
    ← Finset.sum_add_distrib]
  simp_rw [hterm]
  rw [Finset.sum_range_sub', hf0, hfn, sub_zero]

/-- The uncancelled boundary decomposes into edge-disjoint circuits. The sum of their signed
crossings at a cell of the set is one, so at least one circuit has positive index there.
Final draft, Appendix A contour indexing. -/
theorem exists_square_boundary_positive_index (S : Finset Lattice) (z : Lattice)
    (hz : z ∈ S) :
    ∃ (m : ℕ) (v : Fin (m + 1) → Lattice),
      IsSquareCircuit v ∧
      (∀ i, dualEdgeLeftCellCode (squareCircuitEdge v i) ∈ S ∧
        dualEdgeRightCellCode (squareCircuitEdge v i) ∉ S) ∧ 0 < squareRayIndex v z := by
  classical
  obtain ⟨E, hmem, hbalance, _, hreverse, _, _⟩ := exists_balanced_square_boundary S
  obtain ⟨n, m, v, hc, hdis, hcover⟩ :=
    finite_directed_circuit_decomposition E (fun x => (hbalance x).symm)
  have hsum : ∑ j : Fin n, squareRayIndex (v j) z = 1 := by
    rw [← square_boundary_ray_sum hmem hz, ← hcover]
    rw [Finset.sum_biUnion (fun j _ k _ hjk => hdis hjk)]
    apply Finset.sum_congr rfl
    intro j _
    symm
    apply Finset.sum_image
    exact (hc j).2.2.injOn
  have hex : ∃ j : Fin n, 0 < squareRayIndex (v j) z := by
    by_contra hnone
    have hnonpos : ∑ j : Fin n, squareRayIndex (v j) z ≤ 0 :=
      Finset.sum_nonpos (fun j _ => le_of_not_gt (fun hj => hnone ⟨j, hj⟩))
    omega
  obtain ⟨j, hj⟩ := hex
  have he (i : Fin (m j)) : squareCircuitEdge (v j) i ∈ E := by
    rw [← hcover]
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  refine ⟨m j, v j, ⟨(hc j).2.1, fun i => boundary_unit hmem (he i), (hc j).2.2, ?_⟩,
    fun i => boundary_sides hmem (he i), hj⟩
  intro i k h
  apply hreverse _ (he i)
  change (squareCircuitEdge (v j) i).swap ∈ E
  rw [h]
  exact he k

end LPPDifferentiability
