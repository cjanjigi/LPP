/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.Lattice
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
import LPP_Foundations.Model.ClosedLatticeWalkCounts
import Differentiability.Model.OrientedEndpointClosure
import Lean.Elab.Tactic.Omega

/-!
# Bad sites on an oriented boundary walk

The count is for the image of the upward and leftward edge indices
under their left-cell labels. No contour is constructed here.
-/

public section

namespace LPPDifferentiability

/-- A closed signed walk with injective directed edges has at least `m / 8`
distinct left-cell labels on its upward and leftward edges. The incidence
equalities give at most one edge of either direction at a fixed label. -/
theorem closed_lattice_walk_left_cell_image_card
    (m : ℕ) (v : Fin (m + 1) → Lattice)
    (hclosed : v (0 : Fin (m + 1)) = v (Fin.last m))
    (hstep : ∀ i : Fin m,
      v i.succ - v i.castSucc = (0, 1) ∨
      v i.succ - v i.castSucc = (0, -1) ∨
      v i.succ - v i.castSucc = (-1, 0) ∨
      v i.succ - v i.castSucc = (1, 0))
    (hedge_inj : Function.Injective
      (fun i : Fin m => (v i.castSucc, v i.succ)))
    (w : Fin m → Lattice)
    (hinc : ∀ i : Fin m,
      (v i.succ - v i.castSucc = (0, 1) →
        v i.castSucc = ((w i).1 + 1, (w i).2) ∧
        v i.succ = ((w i).1 + 1, (w i).2 + 1)) ∧
      (v i.succ - v i.castSucc = (-1, 0) →
        v i.castSucc = ((w i).1 + 1, (w i).2 + 1) ∧
        v i.succ = ((w i).1, (w i).2 + 1))) :
    let U : Finset (Fin m) := Finset.univ.filter
      (fun i => v i.succ - v i.castSucc = (0, 1))
    let L : Finset (Fin m) := Finset.univ.filter
      (fun i => v i.succ - v i.castSucc = (-1, 0))
    let E : Finset (Fin m) := U ∪ L
    m ≤ 8 * (E.image w).card := by
  classical
  let U : Finset (Fin m) := Finset.univ.filter
    (fun i => v i.succ - v i.castSucc = (0, 1))
  let L : Finset (Fin m) := Finset.univ.filter
    (fun i => v i.succ - v i.castSucc = (-1, 0))
  let E : Finset (Fin m) := U ∪ L
  let I : Finset Lattice := E.image w
  have hbalance : 2 * (U.card + L.card) = m := by
    simpa only [U, L] using
      (closed_lattice_walk_direction_balance m v hclosed hstep).2.2
  have hUinj : Set.InjOn w U := by
    intro i hi j hj hij
    have hiU : i ∈ U := Finset.mem_coe.mp hi
    have hjU : j ∈ U := Finset.mem_coe.mp hj
    have hiup : v i.succ - v i.castSucc = (0, 1) :=
      (Finset.mem_filter.mp (show i ∈ Finset.univ.filter
        (fun k : Fin m => v k.succ - v k.castSucc = (0, 1)) by
          simpa only [U] using hiU)).2
    have hjup : v j.succ - v j.castSucc = (0, 1) :=
      (Finset.mem_filter.mp (show j ∈ Finset.univ.filter
        (fun k : Fin m => v k.succ - v k.castSucc = (0, 1)) by
          simpa only [U] using hjU)).2
    obtain ⟨histart, hiend⟩ := (hinc i).1 hiup
    obtain ⟨hjstart, hjend⟩ := (hinc j).1 hjup
    apply hedge_inj
    change (v i.castSucc, v i.succ) = (v j.castSucc, v j.succ)
    rw [histart, hiend, hjstart, hjend, hij]
  have hLinj : Set.InjOn w L := by
    intro i hi j hj hij
    have hiL : i ∈ L := Finset.mem_coe.mp hi
    have hjL : j ∈ L := Finset.mem_coe.mp hj
    have hileft : v i.succ - v i.castSucc = (-1, 0) :=
      (Finset.mem_filter.mp (show i ∈ Finset.univ.filter
        (fun k : Fin m => v k.succ - v k.castSucc = (-1, 0)) by
          simpa only [L] using hiL)).2
    have hjleft : v j.succ - v j.castSucc = (-1, 0) :=
      (Finset.mem_filter.mp (show j ∈ Finset.univ.filter
        (fun k : Fin m => v k.succ - v k.castSucc = (-1, 0)) by
          simpa only [L] using hjL)).2
    obtain ⟨histart, hiend⟩ := (hinc i).2 hileft
    obtain ⟨hjstart, hjend⟩ := (hinc j).2 hjleft
    apply hedge_inj
    change (v i.castSucc, v i.succ) = (v j.castSucc, v j.succ)
    rw [histart, hiend, hjstart, hjend, hij]
  have hUimage : U.card ≤ I.card := by
    calc
      U.card = (U.image w).card := (Finset.card_image_of_injOn hUinj).symm
      _ ≤ I.card := Finset.card_le_card (by
        intro z hz
        rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
        exact Finset.mem_image.mpr ⟨i, Finset.mem_union_left L hi, rfl⟩)
  have hLimage : L.card ≤ I.card := by
    calc
      L.card = (L.image w).card := (Finset.card_image_of_injOn hLinj).symm
      _ ≤ I.card := Finset.card_le_card (by
        intro z hz
        rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
        exact Finset.mem_image.mpr ⟨i, Finset.mem_union_right U hi, rfl⟩)
  have hsum : U.card + L.card ≤ I.card + I.card := Nat.add_le_add hUimage hLimage
  change m ≤ 8 * I.card
  omega

/-- For natural-quadrant labels on a source boundary, endpoint membership and the
corresponding forward exits make every point in the same finite image bad. The
cardinality bound uses that unchanged image. -/
theorem oriented_boundary_left_cell_bad_sites
    (G : Set (ℕ × ℕ)) (m : ℕ) (v : Fin (m + 1) → Lattice)
    (hclosed : v (0 : Fin (m + 1)) = v (Fin.last m))
    (hstep : ∀ i : Fin m,
      v i.succ - v i.castSucc = (0, 1) ∨
      v i.succ - v i.castSucc = (0, -1) ∨
      v i.succ - v i.castSucc = (-1, 0) ∨
      v i.succ - v i.castSucc = (1, 0))
    (hedge_inj : Function.Injective
      (fun i : Fin m => (v i.castSucc, v i.succ)))
    (w : Fin m → ℕ × ℕ)
    (hinc : ∀ i : Fin m,
      (v i.succ - v i.castSucc = (0, 1) →
        v i.castSucc = (((w i).1 : ℤ) + 1, ((w i).2 : ℤ)) ∧
        v i.succ = (((w i).1 : ℤ) + 1, ((w i).2 : ℤ) + 1)) ∧
      (v i.succ - v i.castSucc = (-1, 0) →
        v i.castSucc = (((w i).1 : ℤ) + 1, ((w i).2 : ℤ) + 1) ∧
        v i.succ = (((w i).1 : ℤ), ((w i).2 : ℤ) + 1)))
    (hR : ∀ i : Fin m,
      (v i.succ - v i.castSucc = (0, 1) →
        w i ∈ {x : ℕ × ℕ | ∃ n : ℕ, ∃ q : Fin (n + 1) → ℕ × ℕ,
          q 0 = (0, 0) ∧ q (Fin.last n) = x ∧
          (∀ j : Fin n,
            q j.succ = q j.castSucc + (1, 0) ∨
            q j.succ = q j.castSucc + (0, 1)) ∧
          ∀ j : Fin (n + 1), (j : ℕ) < n → q j ∈ G}) ∧
      (v i.succ - v i.castSucc = (-1, 0) →
        w i ∈ {x : ℕ × ℕ | ∃ n : ℕ, ∃ q : Fin (n + 1) → ℕ × ℕ,
          q 0 = (0, 0) ∧ q (Fin.last n) = x ∧
          (∀ j : Fin n,
            q j.succ = q j.castSucc + (1, 0) ∨
            q j.succ = q j.castSucc + (0, 1)) ∧
          ∀ j : Fin (n + 1), (j : ℕ) < n → q j ∈ G}))
    (hexit : ∀ i : Fin m,
      (v i.succ - v i.castSucc = (0, 1) →
        w i + (1, 0) ∉ {x : ℕ × ℕ | ∃ n : ℕ, ∃ q : Fin (n + 1) → ℕ × ℕ,
          q 0 = (0, 0) ∧ q (Fin.last n) = x ∧
          (∀ j : Fin n,
            q j.succ = q j.castSucc + (1, 0) ∨
            q j.succ = q j.castSucc + (0, 1)) ∧
          ∀ j : Fin (n + 1), (j : ℕ) < n → q j ∈ G}) ∧
      (v i.succ - v i.castSucc = (-1, 0) →
        w i + (0, 1) ∉ {x : ℕ × ℕ | ∃ n : ℕ, ∃ q : Fin (n + 1) → ℕ × ℕ,
          q 0 = (0, 0) ∧ q (Fin.last n) = x ∧
          (∀ j : Fin n,
            q j.succ = q j.castSucc + (1, 0) ∨
            q j.succ = q j.castSucc + (0, 1)) ∧
          ∀ j : Fin (n + 1), (j : ℕ) < n → q j ∈ G})) :
    let U : Finset (Fin m) := Finset.univ.filter
      (fun i => v i.succ - v i.castSucc = (0, 1))
    let L : Finset (Fin m) := Finset.univ.filter
      (fun i => v i.succ - v i.castSucc = (-1, 0))
    let E : Finset (Fin m) := U ∪ L
    (∀ x ∈ E.image w, x ∉ G) ∧ m ≤ 8 * (E.image w).card := by
  classical
  let U : Finset (Fin m) := Finset.univ.filter
    (fun i => v i.succ - v i.castSucc = (0, 1))
  let L : Finset (Fin m) := Finset.univ.filter
    (fun i => v i.succ - v i.castSucc = (-1, 0))
  let E : Finset (Fin m) := U ∪ L
  let wz : Fin m → Lattice := fun i => (((w i).1 : ℤ), ((w i).2 : ℤ))
  constructor
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    rcases Finset.mem_union.mp (by simpa only [E] using hi) with hiup | hileft
    · have hiup' : v i.succ - v i.castSucc = (0, 1) :=
        (Finset.mem_filter.mp (show i ∈ Finset.univ.filter
          (fun j : Fin m => v j.succ - v j.castSucc = (0, 1)) by
            simpa only [U] using hiup)).2
      exact oriented_endpoint_set_bad_of_forward_exit G (w i)
        ((hR i).1 hiup') (Or.inl ((hexit i).1 hiup'))
    · have hileft' : v i.succ - v i.castSucc = (-1, 0) :=
        (Finset.mem_filter.mp (show i ∈ Finset.univ.filter
          (fun j : Fin m => v j.succ - v j.castSucc = (-1, 0)) by
            simpa only [L] using hileft)).2
      exact oriented_endpoint_set_bad_of_forward_exit G (w i)
        ((hR i).2 hileft') (Or.inr ((hexit i).2 hileft'))
  · have hcountZ : m ≤ 8 * (E.image wz).card :=
      closed_lattice_walk_left_cell_image_card m v hclosed hstep hedge_inj wz
        (by
          intro i
          simpa only [wz] using hinc i)
    have hcast_inj : Function.Injective
        (fun z : ℕ × ℕ => ((z.1 : ℤ), (z.2 : ℤ))) := by
      intro a b hab
      exact Prod.ext (Int.ofNat.inj (congrArg Prod.fst hab))
        (Int.ofNat.inj (congrArg Prod.snd hab))
    let castLabel : ℕ × ℕ → Lattice := fun z => ((z.1 : ℤ), (z.2 : ℤ))
    have hcard : (E.image wz).card = (E.image w).card := by
      have hsets : E.image wz = (E.image w).image castLabel := by
        change E.image (castLabel ∘ w) = (E.image w).image castLabel
        exact Finset.image_image.symm
      rw [hsets]
      exact Finset.card_image_of_injective _ hcast_inj
    calc
      m ≤ 8 * (E.image wz).card := hcountZ
      _ = 8 * (E.image w).card := by rw [hcard]

end LPPDifferentiability
