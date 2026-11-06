/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.SquareBoundaryCircuit
public import Differentiability.Model.BoundaryBadSiteCount
public import Differentiability.Model.OrientedEndpointClosure
import Mathlib.Tactic

/-! The actual finite endpoint set supplies a circuit with bad left labels.
This is a finite geometric step, not the percolation probability bound. -/

public section

namespace LPPDifferentiability

/-- A finite literal endpoint set yields the same actual boundary circuit and
at least `m/8` distinct bad left-cell labels. -/
theorem exists_oriented_endpoint_boundary_circuit
    (G : Set (ℕ × ℕ)) (S : Finset (ℕ × ℕ))
    (hS : ∀ x, x ∈ S ↔ x ∈ {y : ℕ × ℕ | ∃ n : ℕ,
      ∃ q : Fin (n + 1) → ℕ × ℕ,
        q 0 = (0, 0) ∧ q (Fin.last n) = y ∧
        (∀ i : Fin n, q i.succ = q i.castSucc + (1, 0) ∨
          q i.succ = q i.castSucc + (0, 1)) ∧
        ∀ i : Fin (n + 1), (i : ℕ) < n → q i ∈ G}) :
    let T : Finset Lattice := S.image (fun x => ((x.1 : ℤ), (x.2 : ℤ)))
    ∃ (E : Finset (Lattice × Lattice)) (m : ℕ)
      (v : Fin (m + 1) → Lattice) (w : Fin m → ℕ × ℕ),
      (∀ e, e ∈ E ↔ ∃ z, z ∈ T ∧
        ((e = ((z.1, z.2), (z.1 + 1, z.2)) ∧ (z.1, z.2 - 1) ∉ T) ∨
         (e = ((z.1 + 1, z.2), (z.1 + 1, z.2 + 1)) ∧ (z.1 + 1, z.2) ∉ T) ∨
         (e = ((z.1 + 1, z.2 + 1), (z.1, z.2 + 1)) ∧ (z.1, z.2 + 1) ∉ T) ∨
         (e = ((z.1, z.2 + 1), (z.1, z.2)) ∧ (z.1 - 1, z.2) ∉ T))) ∧
      4 ≤ m ∧ v 0 = v (Fin.last m) ∧
      Function.Injective (fun i : Fin m => (v i.castSucc, v i.succ)) ∧
      (∀ i : Fin m, (v i.castSucc, v i.succ) ∈ E) ∧
      (∀ i : Fin m,
        v i.succ - v i.castSucc = (0, 1) ∨
        v i.succ - v i.castSucc = (0, -1) ∨
        v i.succ - v i.castSucc = (-1, 0) ∨
        v i.succ - v i.castSucc = (1, 0)) ∧
      (∑ i : Fin m,
        if (v i.castSucc).2 = 0 ∧ (v i.succ).2 = 1 ∧ 1 ≤ (v i.castSucc).1
        then (1 : ℤ)
        else if (v i.castSucc).2 = 1 ∧ (v i.succ).2 = 0 ∧ 1 ≤ (v i.castSucc).1
        then -1 else 0) = 1 ∧
      (∀ i j : Fin m, (v i.succ, v i.castSucc) ≠ (v j.castSucc, v j.succ)) ∧
      (∀ i, 0 ≤ (v i).1 ∧ (v i).1 ≤ (m : ℤ) + 1 ∧
        0 ≤ (v i).2 ∧ (v i).2 ≤ (m : ℤ) + 1) ∧
      (∀ i : Fin m, w i ∈ S ∧
        (v i.succ - v i.castSucc = (0, 1) →
          v i.castSucc = (((w i).1 : ℤ) + 1, ((w i).2 : ℤ)) ∧
          v i.succ = (((w i).1 : ℤ) + 1, ((w i).2 : ℤ) + 1) ∧ w i + (1, 0) ∉ S) ∧
        (v i.succ - v i.castSucc = (-1, 0) →
          v i.castSucc = (((w i).1 : ℤ) + 1, ((w i).2 : ℤ) + 1) ∧
          v i.succ = (((w i).1 : ℤ), ((w i).2 : ℤ) + 1) ∧ w i + (0, 1) ∉ S)) ∧
      (let A : Finset (Fin m) :=
        (Finset.univ.filter (fun i => v i.succ - v i.castSucc = (0, 1))) ∪
        (Finset.univ.filter (fun i => v i.succ - v i.castSucc = (-1, 0)))
       (∀ x ∈ A.image w, x ∉ G) ∧ m ≤ 8 * (A.image w).card) := by
  classical
  let castSite : (ℕ × ℕ) → Lattice := fun x => ((x.1 : ℤ), (x.2 : ℤ))
  let T : Finset Lattice := S.image castSite
  have hcast_inj : Function.Injective castSite := by
    intro a b hab
    exact Prod.ext (Int.ofNat.inj (congrArg Prod.fst hab))
      (Int.ofNat.inj (congrArg Prod.snd hab))
  have hcast_mem (x : ℕ × ℕ) : castSite x ∈ T ↔ x ∈ S := by
    constructor
    · intro hx
      obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hx
      exact hcast_inj hxy ▸ hy
    · intro hx
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hquad : ∀ x ∈ T, 0 ≤ x.1 ∧ 0 ≤ x.2 := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨Int.natCast_nonneg _, Int.natCast_nonneg _⟩
  have hzero : (0, 0) ∈ T := by
    have hz := (hS (0, 0)).mpr (oriented_endpoint_set_zero G)
    exact Finset.mem_image.mpr ⟨(0, 0), hz, rfl⟩
  obtain ⟨E, m, v, z, hmem, hm, hc, hi, he, hs, _, hindex, hrev, hbox, hz⟩ :=
    exists_square_boundary_circuit T hquad hzero
  let w : Fin m → ℕ × ℕ := fun i => ((z i).1.toNat, (z i).2.toNat)
  have hwcast (i : Fin m) : castSite (w i) = z i := by
    obtain ⟨hx, hy⟩ := hquad _ (hz i).1
    exact Prod.ext (Int.toNat_of_nonneg hx) (Int.toNat_of_nonneg hy)
  have hlabels (i : Fin m) : w i ∈ S ∧
      (v i.succ - v i.castSucc = (0, 1) →
        v i.castSucc = (((w i).1 : ℤ) + 1, ((w i).2 : ℤ)) ∧
        v i.succ = (((w i).1 : ℤ) + 1, ((w i).2 : ℤ) + 1) ∧ w i + (1, 0) ∉ S) ∧
      (v i.succ - v i.castSucc = (-1, 0) →
        v i.castSucc = (((w i).1 : ℤ) + 1, ((w i).2 : ℤ) + 1) ∧
        v i.succ = (((w i).1 : ℤ), ((w i).2 : ℤ) + 1) ∧ w i + (0, 1) ∉ S) := by
    have hcell := hz i
    rw [← hwcast i] at hcell
    refine ⟨(hcast_mem _).mp hcell.1, ?_, ?_⟩
    · intro hu
      obtain ⟨ha, hb, hn⟩ := hcell.2.1 hu
      refine ⟨ha, hb, ?_⟩
      intro hout
      have hncast := (hcast_mem (w i + (1, 0))).mpr hout
      apply hn
      simpa only [castSite, Prod.fst_add, Prod.snd_add, Nat.cast_add,
        Nat.cast_one, Nat.cast_zero, add_zero] using hncast
    · intro hl
      obtain ⟨ha, hb, hn⟩ := hcell.2.2 hl
      refine ⟨ha, hb, ?_⟩
      intro hout
      have hncast := (hcast_mem (w i + (0, 1))).mpr hout
      apply hn
      simpa only [castSite, Prod.fst_add, Prod.snd_add, Nat.cast_add,
        Nat.cast_one, Nat.cast_zero, add_zero] using hncast
  have hbad := oriented_boundary_left_cell_bad_sites G m v hc hs hi w
    (by
      intro i
      exact ⟨fun hu => ⟨((hlabels i).2.1 hu).1, ((hlabels i).2.1 hu).2.1⟩,
        fun hl => ⟨((hlabels i).2.2 hl).1, ((hlabels i).2.2 hl).2.1⟩⟩)
    (by
      intro i
      exact ⟨fun _ => (hS _).mp (hlabels i).1, fun _ => (hS _).mp (hlabels i).1⟩)
    (by
      intro i
      constructor
      · intro hu hneighbor
        exact ((hlabels i).2.1 hu).2.2 ((hS _).mpr hneighbor)
      · intro hl hneighbor
        exact ((hlabels i).2.2 hl).2.2 ((hS _).mpr hneighbor))
  exact ⟨E, m, v, w, hmem, hm, hc, hi, he, hs, hindex, hrev, hbox, hlabels, hbad⟩

end LPPDifferentiability
