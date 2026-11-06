/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.FiniteBoxWalkCount
public import Differentiability.Model.ContourNaturalLabels
public import Differentiability.Model.OrientedClusterContour
import Mathlib.Tactic

/-! A deterministic countable cover by finite walks and their natural labels. -/

public section

namespace LPPDifferentiability

/-- The walk families and their natural left-square labels are chosen
before the good set. The families are filtered counted walks, including open
walks; the finite-cluster circuit belongs to one of these families. -/
theorem exists_contour_bad_label_cover :
    ∃ W : (n : ℕ) → Finset (Fin (n + 5) → Lattice),
    ∃ B : (n : ℕ) → {u // u ∈ W n} → Finset (ℕ × ℕ),
      (∀ n, (W n).card ≤ (n + 6) ^ 2 * 4 * 3 ^ (n + 3)) ∧
      (∀ n (v : {u // u ∈ W n}),
        (∀ i, 0 ≤ (v.val i).1 ∧ (v.val i).1 ≤ ((n + 4 : ℕ) : ℤ) + 1 ∧
          0 ≤ (v.val i).2 ∧ (v.val i).2 ≤ ((n + 4 : ℕ) : ℤ) + 1) ∧
        (∀ i : Fin (n + 4), v.val i.succ - v.val i.castSucc = (0, 1) ∨
          v.val i.succ - v.val i.castSucc = (0, -1) ∨
          v.val i.succ - v.val i.castSucc = (-1, 0) ∨
          v.val i.succ - v.val i.castSucc = (1, 0)) ∧
        (∀ (i : ℕ) (hi : i + 2 ≤ n + 4),
          v.val ⟨i + 2, by omega⟩ ≠ v.val ⟨i, by omega⟩) ∧
        (∀ x : ℕ × ℕ, x ∈ B n v ↔ ∃ i : Fin (n + 4),
          (v.val i.castSucc = ((x.1 : ℤ) + 1, (x.2 : ℤ)) ∧
            v.val i.succ = ((x.1 : ℤ) + 1, (x.2 : ℤ) + 1)) ∨
          (v.val i.castSucc = ((x.1 : ℤ) + 1, (x.2 : ℤ) + 1) ∧
            v.val i.succ = ((x.1 : ℤ), (x.2 : ℤ) + 1))) ∧
        (B n v).card ≤ n + 4 ∧ n + 4 ≤ 8 * (B n v).card) ∧
      (∀ G : Set (ℕ × ℕ),
        (¬ ∃ q : ℕ → ℕ × ℕ, q 0 = (0, 0) ∧
          (∀ i, q (i + 1) = q i + (1, 0) ∨ q (i + 1) = q i + (0, 1)) ∧
          ∀ i, q i ∈ G) →
        ∃ (n : ℕ) (v : {u // u ∈ W n}), ∀ x ∈ B n v, x ∉ G) := by
  classical
  choose U hU hcU using fun n : ℕ =>
    exists_finset_nonbacktracking_walks_in_box (n + 4) (by omega)
  let T (n : ℕ) := (U n).filter (fun v =>
    ∀ i, 0 ≤ (v i).1 ∧ (v i).1 ≤ ((n + 4 : ℕ) : ℤ) + 1 ∧
      0 ≤ (v i).2 ∧ (v i).2 ≤ ((n + 4 : ℕ) : ℤ) + 1)
  have hTbox (n : ℕ) (v : {u // u ∈ T n}) :
      ∀ i, 0 ≤ (v.val i).1 ∧ (v.val i).1 ≤ ((n + 4 : ℕ) : ℤ) + 1 ∧
        0 ≤ (v.val i).2 ∧ (v.val i).2 ≤ ((n + 4 : ℕ) : ℤ) + 1 :=
    (Finset.mem_filter.mp v.property).2
  choose L hLmem hLcard hLuniq hLag using fun n (v : {u // u ∈ T n}) =>
    exists_contour_natural_labels (n + 4) v.val (hTbox n v)
  let W (n : ℕ) := (T n).filter (fun v =>
    ∃ hv : v ∈ T n, n + 4 ≤ 8 * (L n ⟨v, hv⟩).card)
  let B (n : ℕ) (v : {u // u ∈ W n}) :=
    L n ⟨v.val, (Finset.mem_filter.mp v.property).1⟩
  refine ⟨W, B, ?_, ?_, ?_⟩
  · intro n
    calc
      (W n).card ≤ (T n).card := Finset.card_filter_le _ _
      _ ≤ (U n).card := Finset.card_filter_le _ _
      _ ≤ (n + 6) ^ 2 * 4 * 3 ^ (n + 3) := by
        simpa only [show n + 4 - 1 = n + 3 by omega] using hcU n
  · intro n v
    have hvT := (Finset.mem_filter.mp v.property).1
    have hvU := (Finset.mem_filter.mp hvT).1
    have hwalk := (hU n v.val).mp hvU
    obtain ⟨hv, hfactor⟩ := (Finset.mem_filter.mp v.property).2
    exact ⟨hTbox n ⟨v.val, hvT⟩, hwalk.2.2.1, hwalk.2.2.2,
      hLmem n ⟨v.val, hvT⟩, hLcard n ⟨v.val, hvT⟩, hfactor⟩
  · intro G hno
    obtain ⟨_S, _hS, _E, m, v, w, _hE, hm, _hclosed, _hinj, _hedges,
      hsteps, _hcross, hreverse, hbox, hw, hbad, hfactor⟩ :=
      exists_finite_oriented_cluster_boundary_circuit G hno
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n + 4 := ⟨m - 4, by omega⟩
    have hnb : ∀ (i : ℕ) (hi : i + 2 ≤ n + 4),
        v ⟨i + 2, by omega⟩ ≠ v ⟨i, by omega⟩ := by
      intro i hi hreturn
      apply hreverse ⟨i, by omega⟩ ⟨i + 1, by omega⟩
      exact Prod.ext rfl hreturn.symm
    have hvU : v ∈ U n := (hU n v).mpr
      ⟨⟨(hbox 0).1, (hbox 0).2.1⟩,
        ⟨(hbox 0).2.2.1, (hbox 0).2.2.2⟩, hsteps, hnb⟩
    have hvT : v ∈ T n := Finset.mem_filter.mpr ⟨hvU, hbox⟩
    have hag := hLag n ⟨v, hvT⟩ w (fun i =>
      ⟨fun hu => ⟨((hw i).2.1 hu).1, ((hw i).2.1 hu).2.1⟩,
       fun hl => ⟨((hw i).2.2 hl).1, ((hw i).2.2 hl).2.1⟩⟩)
    have hvW : v ∈ W n := Finset.mem_filter.mpr
      ⟨hvT, hvT, by rw [hag]; exact hfactor⟩
    refine ⟨n, ⟨v, hvW⟩, ?_⟩
    change ∀ x ∈ L n ⟨v, hvT⟩, x ∉ G
    rw [hag]
    exact hbad

end LPPDifferentiability
