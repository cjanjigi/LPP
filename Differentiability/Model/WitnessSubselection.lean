/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Algebra.BigOperators.Fin
import Differentiability.Model.WitnessAllocationSelection
import Mathlib.Data.Fintype.EquivFin

/-! Finite indexed subselections with exact counts at each stage. -/

@[expose] public section

open scoped BigOperators

namespace LPPDifferentiability

/-- Capacities contain an exact-size indexed subselection, enumerated by Fin t.
The returned stage multiplicity is the exact size of each fiber of the enumeration. -/
theorem exists_witness_subselection_enumeration {N t : ℕ}
    (capacity : Fin (N + 1) → ℕ)
    (ht : t ≤ ∑ i : Fin (N + 1), capacity i) :
    ∃ multiplicity : Fin (N + 1) → ℕ,
      (∀ i, multiplicity i ≤ capacity i) ∧
      (∑ i : Fin (N + 1), multiplicity i) = t ∧
      ∃ g : Fin t → Σ i : Fin (N + 1), Fin (capacity i),
        Function.Injective g ∧
        ∀ i, Fintype.card {j : Fin t // (g j).1 = i} = multiplicity i := by
  classical
  obtain ⟨multiplicity, hcapacity, htotal⟩ :=
    exists_witness_allocation_below_of_le_sum capacity ht
  have hcard :
      Fintype.card (Fin t) =
        Fintype.card (Σ i : Fin (N + 1), Fin (multiplicity i)) := by
    simpa only [Fintype.card_fin, Fintype.card_sigma] using htotal.symm
  let e : Fin t ≃ Σ i : Fin (N + 1), Fin (multiplicity i) :=
    Fintype.equivOfCardEq hcard
  let embedStage : (i : Fin (N + 1)) → Fin (multiplicity i) → Fin (capacity i) :=
    fun i j => ⟨j.val, Nat.lt_of_lt_of_le j.isLt (hcapacity i)⟩
  let embed : (Σ i : Fin (N + 1), Fin (multiplicity i)) →
      Σ i : Fin (N + 1), Fin (capacity i) :=
    fun x => ⟨x.1, embedStage x.1 x.2⟩
  let g : Fin t → Σ i : Fin (N + 1), Fin (capacity i) := fun j => embed (e j)
  have hembed : Function.Injective embed := by
    rintro ⟨i, j⟩ ⟨k, l⟩ h
    have hi : i = k := congrArg Sigma.fst h
    subst k
    have hj : j.val = l.val :=
      congrArg (fun x : Σ i : Fin (N + 1), Fin (capacity i) => x.2.val) h
    have hfin : j = l := Fin.ext hj
    subst l
    rfl
  have hg : Function.Injective g := hembed.comp e.injective
  have hstageFiber (i : Fin (N + 1)) :
      {j : Fin t // (g j).1 = i} ≃ Fin (multiplicity i) := by
    let e₁ :
        {j : Fin t // (g j).1 = i} ≃
          {x : Σ k : Fin (N + 1), Fin (multiplicity k) // x.1 = i} :=
      e.subtypeEquiv (by intro j; rfl)
    let e₂ :
        {x : Σ k : Fin (N + 1), Fin (multiplicity k) // x.1 = i} ≃
          Fin (multiplicity i) :=
      { toFun := fun x => by
          rcases x with ⟨⟨k, j⟩, hki⟩
          cases hki
          exact j
        invFun := fun j => ⟨⟨i, j⟩, rfl⟩
        left_inv := by
          rintro ⟨⟨k, j⟩, hki⟩
          cases hki
          rfl
        right_inv := by
          intro j
          rfl }
    exact e₁.trans e₂
  refine ⟨multiplicity, hcapacity, htotal, g, hg, ?_⟩
  intro i
  have h := Fintype.card_congr (hstageFiber i)
  simpa only [Fintype.card_fin] using h

end LPPDifferentiability
