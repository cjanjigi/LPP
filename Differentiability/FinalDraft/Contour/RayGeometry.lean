/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.FinalDraft.Contour.BoundaryIndex
import LPP_Foundations.Model.ClosedLatticeWalkCounts
import Mathlib.Tactic

/-! Occupied coordinate lines and the ray length bound for a positive-index square circuit. -/

public section

namespace LPPDifferentiability

private theorem sum_telescope {m : ℕ} (v : Fin (m + 1) → Lattice)
    (hclosed : v 0 = v (Fin.last m)) (f : Lattice → ℤ) :
    ∑ i : Fin m, (f (v i.succ) - f (v i.castSucc)) = 0 := by
  have h₁ := Fin.sum_univ_succ (fun j : Fin (m + 1) => f (v j))
  have h₂ := Fin.sum_univ_castSucc (fun j : Fin (m + 1) => f (v j))
  rw [← hclosed] at h₂
  rw [Finset.sum_sub_distrib]
  omega

private def squareNorthCrossing (z : Lattice) (e : Lattice × Lattice) : ℤ :=
  if e.1.1 = z.1 + 1 ∧ e.2.1 = z.1 ∧ z.2 + 1 ≤ e.1.2 then 1
  else if e.1.1 = z.1 ∧ e.2.1 = z.1 + 1 ∧ z.2 + 1 ≤ e.1.2 then -1 else 0

private theorem east_eq_north_index {m : ℕ} {v : Fin (m + 1) → Lattice}
    (hc : IsSquareCircuit v) (z : Lattice) :
    squareRayIndex v z = ∑ i : Fin m, squareNorthCrossing z (squareCircuitEdge v i) := by
  apply sub_eq_zero.mp
  rw [squareRayIndex, ← Finset.sum_sub_distrib]
  let f : Lattice → ℤ := fun u => if z.1 + 1 ≤ u.1 ∧ z.2 + 1 ≤ u.2 then 1 else 0
  rw [← sum_telescope v hc.1 f]
  apply Finset.sum_congr rfl
  intro i _
  have hcoord := dual_unit_edge_cases (hc.2.1 i)
  simp only [squareRayCrossing, squareNorthCrossing, squareCircuitEdge, f]
  split_ifs <;> omega

private theorem exists_positive_east_crossing {m : ℕ} {v : Fin (m + 1) → Lattice}
    (z : Lattice) (hz : 0 < squareRayIndex v z) :
    ∃ i : Fin m, (v i.castSucc).2 = z.2 ∧ (v i.succ).2 = z.2 + 1 ∧
      z.1 + 1 ≤ (v i.castSucc).1 := by
  by_contra hn
  have hnonpos : squareRayIndex v z ≤ 0 := by
    apply Finset.sum_nonpos
    intro i _
    simp only [squareRayCrossing, squareCircuitEdge]
    split_ifs with h
    · exact (hn ⟨i, h⟩).elim
    all_goals omega
  omega

private theorem exists_positive_north_crossing {m : ℕ} {v : Fin (m + 1) → Lattice}
    (hc : IsSquareCircuit v) (z : Lattice) (hz : 0 < squareRayIndex v z) :
    ∃ i : Fin m, (v i.castSucc).1 = z.1 + 1 ∧ (v i.succ).1 = z.1 ∧
      z.2 + 1 ≤ (v i.castSucc).2 := by
  rw [east_eq_north_index hc] at hz
  by_contra hn
  have hnonpos : ∑ i : Fin m, squareNorthCrossing z (squareCircuitEdge v i) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i _
    simp only [squareNorthCrossing, squareCircuitEdge]
    split_ifs with h
    · exact (hn ⟨i, h⟩).elim
    all_goals omega
  omega

/-- The circuit has at least two horizontal edges per occupied column and two vertical
edges per occupied row. The area and minimum perimeter bounds follow. Final draft,
Lemma `lem:contour` area and side-count clauses. -/
theorem square_circuit_card_le {S : Finset Lattice} {m : ℕ}
    {v : Fin (m + 1) → Lattice} (hc : IsSquareCircuit v) (hne : S.Nonempty)
    (hpositive : ∀ z ∈ S, 0 < squareRayIndex v z) :
    4 ≤ m ∧ 16 * S.card ≤ m ^ 2 := by
  classical
  let U := Finset.univ.filter (fun i : Fin m => v i.succ - v i.castSucc = (0, 1))
  let L := Finset.univ.filter (fun i : Fin m => v i.succ - v i.castSucc = (-1, 0))
  let A := S.image Prod.fst
  let B := S.image Prod.snd
  have hB : B.card ≤ U.card := by
    refine (Finset.card_le_card (t := U.image (fun i => (v i.castSucc).2)) ?_).trans Finset.card_image_le
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨i, hfirst, hlast, _⟩ := exists_positive_east_crossing z (hpositive z hz)
    apply Finset.mem_image.mpr
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hfirst⟩
    have hcoord := dual_unit_edge_cases (hc.2.1 i)
    apply Prod.ext <;> simp only [Prod.fst_sub, Prod.snd_sub] <;> omega
  have hA : A.card ≤ L.card := by
    refine (Finset.card_le_card (t := L.image (fun i => (v i.succ).1)) ?_).trans Finset.card_image_le
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨i, hfirst, hlast, _⟩ := exists_positive_north_crossing hc z (hpositive z hz)
    apply Finset.mem_image.mpr
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hlast⟩
    have hcoord := dual_unit_edge_cases (hc.2.1 i)
    apply Prod.ext <;> simp only [Prod.fst_sub, Prod.snd_sub] <;> omega
  have hbalance : 2 * (U.card + L.card) = m :=
    (closed_lattice_walk_direction_balance m v hc.1 hc.2.1).2.2
  have hperim : 2 * (A.card + B.card) ≤ m := by omega
  have hApos : 0 < A.card := Finset.card_pos.mpr (hne.image _)
  have hBpos : 0 < B.card := Finset.card_pos.mpr (hne.image _)
  have hS : S.card ≤ A.card * B.card := by
    rw [← Finset.card_product]
    exact Finset.card_le_card (fun z hz => Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem Prod.fst hz, Finset.mem_image_of_mem Prod.snd hz⟩)
  refine ⟨by omega, ?_⟩
  calc
    16 * S.card ≤ 16 * (A.card * B.card) := Nat.mul_le_mul_left _ hS
    _ ≤ (2 * (A.card + B.card)) ^ 2 := by
      have hsq : 0 ≤ ((A.card : ℤ) - B.card) ^ 2 := sq_nonneg _
      zify
      nlinarith only [hsq]
    _ ≤ m ^ 2 := Nat.pow_le_pow_left hperim _

private theorem two_abs_le_variation {m : ℕ} (f : Fin (m + 1) → ℤ)
    (hf : f 0 = f (Fin.last m)) (p q : Fin (m + 1)) :
    2 * |f q - f p| ≤ ∑ i : Fin m, |f i.succ - f i.castSucc| := by
  let g : ℕ → ℤ := fun n => f ⟨min n m, by omega⟩
  have hg : ∀ n (hn : n ≤ m), g n = f ⟨n, by omega⟩ :=
    fun n hn => by simp only [g, min_eq_left hn]
  have hsum : ∑ i : Fin m, |f i.succ - f i.castSucc| =
      ∑ i ∈ Finset.range m, |g (i + 1) - g i| := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => |g (i + 1) - g i|) m]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hg (i + 1) (by omega), hg i (by omega)]
    rfl
  have harc : ∀ a b : ℕ, a ≤ b → |g b - g a| ≤ ∑ i ∈ Finset.Ico a b, |g (i + 1) - g i| := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => simp
    | succ b hab ih =>
      rw [Finset.sum_Ico_succ_top hab]
      linarith only [ih, abs_sub_le (g (b + 1)) (g b) (g a)]
  have hgclosed : g m = g 0 := by rw [hg m le_rfl, hg 0 (Nat.zero_le _)]; exact hf.symm
  have hsplit (a b : ℕ) (hab : a ≤ b) (hbm : b ≤ m) :
      2 * |g b - g a| ≤ ∑ i ∈ Finset.range m, |g (i + 1) - g i| := by
    have harc₁ := harc 0 a (Nat.zero_le _)
    have harc₂ := harc a b hab
    have harc₃ := harc b m hbm
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le b) hbm,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le a) hab]
    have htriangle := abs_sub_le (g b) (g 0) (g a)
    rw [hgclosed, abs_sub_comm (g 0) (g b)] at harc₃
    rw [abs_sub_comm (g a) (g 0)] at harc₁
    linarith only [harc₁, harc₂, harc₃, htriangle]
  rw [hsum]
  by_cases hpq : p.val ≤ q.val
  · have h := hsplit p.val q.val hpq (by omega)
    rwa [hg p.val (by omega), hg q.val (by omega)] at h
  · have h := hsplit q.val p.val (by omega) (by omega)
    rwa [hg p.val (by omega), hg q.val (by omega), abs_sub_comm] at h

/-- A positive-index circuit meets the first half-perimeter many primal edges of the
positive horizontal ray. Final draft, Lemma `lem:contour`, count clause. -/
theorem square_circuit_hits_ray {m : ℕ} {v : Fin (m + 1) → Lattice}
    (hc : IsSquareCircuit v) (z : Lattice) (hz : 0 < squareRayIndex v z) :
    SquareCircuitHitsRay z v := by
  let f : Lattice → ℤ := fun w => if z.2 + 1 ≤ w.2 then 1 else 0
  obtain ⟨i, hfirst, hlast, hpos⟩ := exists_positive_east_crossing z hz
  have hx : (v i.succ).1 = (v i.castSucc).1 := by
    have hcoord := dual_unit_edge_cases (hc.2.1 i)
    omega
  have hwest : ∃ k : Fin m, (v k.castSucc).1 ≤ z.1 ∧
      (((v k.castSucc).2 = z.2 ∧ (v k.succ).2 = z.2 + 1) ∨
       ((v k.castSucc).2 = z.2 + 1 ∧ (v k.succ).2 = z.2)) := by
    by_contra hn
    have hterm (k : Fin m) :
        squareRayCrossing z (squareCircuitEdge v k) = f (v k.succ) - f (v k.castSucc) := by
      have hcoord := dual_unit_edge_cases (hc.2.1 k)
      have hk : ¬ ((v k.castSucc).1 ≤ z.1 ∧
          (((v k.castSucc).2 = z.2 ∧ (v k.succ).2 = z.2 + 1) ∨
           ((v k.castSucc).2 = z.2 + 1 ∧ (v k.succ).2 = z.2))) :=
        fun h => hn ⟨k, h⟩
      simp only [squareRayCrossing, squareCircuitEdge, f]
      split_ifs <;> omega
    have hzero := sum_telescope v hc.1 f
    unfold squareRayIndex at hz
    simp_rw [hterm] at hz
    omega
  obtain ⟨k, hk, _⟩ := hwest
  have hArc := two_abs_le_variation (fun t => (v t).1) (congrArg Prod.fst hc.1)
    k.castSucc i.castSucc
  have hvariation : ∑ t : Fin m, |(v t.succ).1 - (v t.castSucc).1| ≤ (m : ℤ) := by
    calc
      _ ≤ ∑ _t : Fin m, (1 : ℤ) := by
        apply Finset.sum_le_sum
        intro t _
        have hcoord := dual_unit_edge_cases (hc.2.1 t)
        simp only [abs_eq_max_neg]
        omega
      _ = (m : ℤ) := by simp
  let j : ℕ := ((v i.castSucc).1 - z.1).toNat
  have hj : (j : ℤ) = (v i.castSucc).1 - z.1 := Int.toNat_of_nonneg (by omega)
  have hbound := le_abs_self ((v i.castSucc).1 - (v k.castSucc).1)
  refine ⟨j, by omega, by omega, i, Or.inl ?_⟩
  exact Prod.ext (Prod.ext (by simp only [squareCircuitRayEdge, squareCircuitEdge]; omega) hfirst)
    (Prod.ext (by simp only [squareCircuitRayEdge, squareCircuitEdge]; omega) hlast)

end LPPDifferentiability
