/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.FiniteDirectedClosedTrail

/-! Balance of the edge image of a closed family, and of its removal. -/

public section

namespace LPPDifferentiability

/-- A closed edge-simple family has the same used outgoing and incoming counts. -/
theorem closed_directed_trail_balance {V : Type*} [DecidableEq V]
    (m : ℕ) (v : Fin (m + 1) → V)
    (hc : v 0 = v (Fin.last m))
    (hi : Function.Injective (fun i : Fin m => (v i.castSucc, v i.succ))) (x : V) :
    ((Finset.univ.image (fun i : Fin m => (v i.castSucc, v i.succ))).filter
      (fun e => e.1 = x)).card =
    ((Finset.univ.image (fun i : Fin m => (v i.castSucc, v i.succ))).filter
      (fun e => e.2 = x)).card := by
  have h := directed_trail_endpoint_count m v hi x
  rw [hc] at h
  exact Nat.add_right_cancel h

/-- Removing the edge image of a closed edge-simple family preserves balance. -/
theorem closed_directed_trail_removal {V : Type*} [DecidableEq V]
    (E : Finset (V × V))
    (hb : ∀ x : V, (E.filter (fun e => e.1 = x)).card =
      (E.filter (fun e => e.2 = x)).card)
    (m : ℕ) (v : Fin (m + 1) → V)
    (hc : v 0 = v (Fin.last m))
    (hi : Function.Injective (fun i : Fin m => (v i.castSucc, v i.succ)))
    (he : ∀ i : Fin m, (v i.castSucc, v i.succ) ∈ E) (x : V) :
    ((E \ Finset.univ.image (fun i : Fin m => (v i.castSucc, v i.succ))).filter
      (fun e => e.1 = x)).card =
    ((E \ Finset.univ.image (fun i : Fin m => (v i.castSucc, v i.succ))).filter
      (fun e => e.2 = x)).card := by
  classical
  let C := Finset.univ.image (fun i : Fin m => (v i.castSucc, v i.succ))
  have hCE : C ⊆ E := by
    intro e hh
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hh
    exact he i
  have hfilter (p : V × V → Prop) [DecidablePred p] :
      (E \ C).filter p = E.filter p \ C.filter p := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    tauto
  change ((E \ C).filter (fun e => e.1 = x)).card =
    ((E \ C).filter (fun e => e.2 = x)).card
  rw [hfilter, hfilter,
    Finset.card_sdiff_of_subset (Finset.filter_subset_filter _ hCE),
    Finset.card_sdiff_of_subset (Finset.filter_subset_filter _ hCE),
    hb x, closed_directed_trail_balance m v hc hi x]

end LPPDifferentiability
