/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.ClosedTrailRemoval
public import Mathlib.Data.Finset.Union

/-! Decomposition into closed edge-simple directed vertex families. -/

public section

namespace LPPDifferentiability

/-- A finite balanced directed edge set is exactly the disjoint union of the
edge images of finitely many positive closed edge-simple vertex families. -/
theorem finite_directed_circuit_decomposition {V : Type*} [DecidableEq V]
    (E : Finset (V × V))
    (hb : ∀ x : V, (E.filter (fun e => e.1 = x)).card =
      (E.filter (fun e => e.2 = x)).card) :
    ∃ (n : ℕ) (m : Fin n → ℕ) (v : (j : Fin n) → Fin (m j + 1) → V),
      (∀ j, 0 < m j ∧ v j 0 = v j (Fin.last (m j)) ∧
        Function.Injective (fun i : Fin (m j) => (v j i.castSucc, v j i.succ))) ∧
      Pairwise (fun j k => Disjoint
        (Finset.univ.image (fun i : Fin (m j) => (v j i.castSucc, v j i.succ)))
        (Finset.univ.image (fun i : Fin (m k) => (v k i.castSucc, v k i.succ)))) ∧
      Finset.univ.biUnion (fun j =>
        Finset.univ.image (fun i : Fin (m j) => (v j i.castSucc, v j i.succ))) = E := by
  classical
  induction E using Finset.strongInductionOn with
  | _ E ih =>
    by_cases hne : E.Nonempty
    · obtain ⟨l, w, hl, hc, hi, he⟩ := finite_balanced_closed_trail E hne hb
      let C := Finset.univ.image (fun i : Fin l => (w i.castSucc, w i.succ))
      have hCE : C ⊆ E := by
        intro e hh
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hh
        exact he i
      have hCn : C.Nonempty :=
        ⟨(w (Fin.castSucc ⟨0, hl⟩), w (Fin.succ ⟨0, hl⟩)),
          Finset.mem_image.mpr ⟨⟨0, hl⟩, Finset.mem_univ _, rfl⟩⟩
      obtain ⟨n, m, v, hq, hd, hu⟩ := ih (E \ C) (Finset.sdiff_ssubset hCE hCn)
        (closed_directed_trail_removal E hb l w hc hi he)
      have htail (j : Fin n) :
          Finset.univ.image (fun i : Fin (m j) => (v j i.castSucc, v j i.succ)) ⊆ E \ C := by
        intro e hh
        rw [← hu]
        exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hh⟩
      have hdis (j : Fin n) : Disjoint C
          (Finset.univ.image (fun i : Fin (m j) => (v j i.castSucc, v j i.succ))) := by
        apply Finset.disjoint_left.mpr
        intro e heC hev
        exact (Finset.mem_sdiff.mp (htail j hev)).2 heC
      let lengths : Fin (n + 1) → ℕ := Fin.cons l m
      let vertices : (j : Fin (n + 1)) → Fin (lengths j + 1) → V :=
        @Fin.cases n (fun j => Fin (lengths j + 1) → V) w v
      refine ⟨n + 1, lengths, vertices, ?_, ?_, ?_⟩
      · intro j
        induction j using Fin.cases with
        | zero =>
          change 0 < l ∧ w 0 = w (Fin.last l) ∧
            Function.Injective (fun i : Fin l => (w i.castSucc, w i.succ))
          exact ⟨hl, hc, hi⟩
        | succ j =>
          change 0 < m j ∧ v j 0 = v j (Fin.last (m j)) ∧
            Function.Injective (fun i : Fin (m j) => (v j i.castSucc, v j i.succ))
          exact hq j
      · intro j k hjk
        induction j using Fin.cases with
        | zero =>
          induction k using Fin.cases with
          | zero => exact (hjk rfl).elim
          | succ k =>
            change Disjoint C (Finset.univ.image
              (fun i : Fin (m k) => (v k i.castSucc, v k i.succ)))
            exact hdis k
        | succ j =>
          induction k using Fin.cases with
          | zero =>
            change Disjoint (Finset.univ.image
              (fun i : Fin (m j) => (v j i.castSucc, v j i.succ))) C
            exact (hdis j).symm
          | succ k =>
            change Disjoint (Finset.univ.image
              (fun i : Fin (m j) => (v j i.castSucc, v j i.succ)))
              (Finset.univ.image (fun i : Fin (m k) => (v k i.castSucc, v k i.succ)))
            exact hd (fun h => hjk (congrArg Fin.succ h))
      · ext e
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨j, hj⟩
          induction j using Fin.cases with
          | zero =>
            change e ∈ C at hj
            exact hCE hj
          | succ j =>
            change e ∈ Finset.univ.image
              (fun i : Fin (m j) => (v j i.castSucc, v j i.succ)) at hj
            exact (Finset.mem_sdiff.mp (htail j hj)).1
        · intro heE
          by_cases heC : e ∈ C
          · refine ⟨0, ?_⟩
            change e ∈ C
            exact heC
          · have heR : e ∈ E \ C := Finset.mem_sdiff.mpr ⟨heE, heC⟩
            rw [← hu] at heR
            obtain ⟨j, _, hej⟩ := Finset.mem_biUnion.mp heR
            refine ⟨j.succ, ?_⟩
            change e ∈ Finset.univ.image
              (fun i : Fin (m j) => (v j i.castSucc, v j i.succ))
            exact hej
    · have hE : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst E
      refine ⟨0, Fin.elim0, (fun j => Fin.elim0 j), ?_, ?_, ?_⟩
      · exact fun j => Fin.elim0 j
      · exact fun j => Fin.elim0 j
      · simp

end LPPDifferentiability
