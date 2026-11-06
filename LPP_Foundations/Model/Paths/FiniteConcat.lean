/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Paths.WeightConcat
import Mathlib.Algebra.BigOperators.Fin
import Lean.Elab.Tactic.Omega

/-! Finite concatenation of given actual paths along a compatible chain. -/

@[expose] public section

open scoped BigOperators

namespace LPPDifferentiability

namespace Path

private theorem transport_vertex {a b : Lattice} {d : ℕ × ℕ}
    (h : a = b) (p : Path a d) (i : Fin (d.1 + d.2 + 1)) :
    (h ▸ p : Path b d).vertex i = p.vertex i := by
  cases h
  rfl

private theorem exists_concat_succ (n : ℕ) (ω : Environment) :
    ∀ {u : Fin (n + 2) → Lattice} {d : Fin (n + 1) → ℕ × ℕ},
      (hjoin : ∀ j, u j.succ = u j.castSucc +
        (((d j).1 : ℤ), ((d j).2 : ℤ))) →
      (p : ∀ j, Path (u j.castSucc) (d j)) →
      ∃ q : Path (u (Fin.castSucc (0 : Fin (n + 1))))
          (∑ j : Fin (n + 1), d j),
        pathWeight ω q = ∑ j : Fin (n + 1), pathWeight ω (p j) ∧
        q.vertex (Fin.last ((∑ j : Fin (n + 1), d j).1 +
          (∑ j : Fin (n + 1), d j).2)) = u (Fin.last (n + 1)) ∧
        ∀ i : Fin ((∑ j : Fin (n + 1), d j).1 +
            (∑ j : Fin (n + 1), d j).2 + 1),
          ∃ j : Fin (n + 1), ∃ k : Fin ((d j).1 + (d j).2 + 1),
            q.vertex i = (p j).vertex k := by
  induction n with
  | zero =>
      intro u d hjoin p
      have hsum : (∑ j : Fin 1, d j) = d 0 := by
        exact Fin.sum_univ_one d
      rw [hsum]
      refine ⟨p 0, ?_, ?_, ?_⟩
      · rw [Fin.sum_univ_one]
      · calc
          (p 0).vertex (Fin.last ((d 0).1 + (d 0).2)) =
              u ((0 : Fin 1).castSucc) + (((d 0).1 : ℤ), ((d 0).2 : ℤ)) :=
            (p 0).finish
          _ = u ((0 : Fin 1).succ) := (hjoin 0).symm
          _ = u (Fin.last 1) := by congr 1
      · intro i
        exact ⟨0, i, rfl⟩
  | succ n ih =>
      intro u d hjoin p
      let uTail : Fin (n + 2) → Lattice := fun j => u j.succ
      let dTail : Fin (n + 1) → ℕ × ℕ := fun j => d j.succ
      let hshift : ∀ j : Fin (n + 1), (j.castSucc).succ = (j.succ).castSucc :=
        fun j => Fin.ext rfl
      let pTail : ∀ j, Path (uTail j.castSucc) (dTail j) := fun j => by
        dsimp only [uTail, dTail]
        exact (hshift j).symm ▸ p j.succ
      have hjoinTail : ∀ j, uTail j.succ =
          uTail j.castSucc + (((dTail j).1 : ℤ), ((dTail j).2 : ℤ)) := by
        intro j
        simpa only [uTail, dTail, hshift] using hjoin j.succ
      obtain ⟨r, hrWeight, hrEnd, hrVertices⟩ :=
        ih (u := uTail) (d := dTail) hjoinTail pTail
      have hstart : uTail 0 = u ((0 : Fin (n + 2)).castSucc) +
          (((d 0).1 : ℤ), ((d 0).2 : ℤ)) := by
        simpa only [uTail] using hjoin 0
      let rAligned : Path (u ((0 : Fin (n + 2)).castSucc) +
          (((d 0).1 : ℤ), ((d 0).2 : ℤ)))
          (∑ j : Fin (n + 1), dTail j) :=
        hstart ▸ r
      have hrAlignedVertex (k : Fin ((∑ j : Fin (n + 1), dTail j).1 +
          (∑ j : Fin (n + 1), dTail j).2 + 1)) :
          rAligned.vertex k = r.vertex k := by
        exact transport_vertex hstart r k
      have hrWeightAligned : pathWeight ω rAligned = pathWeight ω r := by
        change (∑ i : Fin ((∑ j : Fin (n + 1), dTail j).1 +
            (∑ j : Fin (n + 1), dTail j).2), ω (rAligned.vertex i.castSucc)) =
          ∑ i : Fin ((∑ j : Fin (n + 1), dTail j).1 +
            (∑ j : Fin (n + 1), dTail j).2), ω (r.vertex i.castSucc)
        apply Finset.sum_congr rfl
        intro i _
        exact congrArg ω (hrAlignedVertex i.castSucc)
      have hpTailVertex (j : Fin (n + 1))
          (k : Fin ((dTail j).1 + (dTail j).2 + 1)) :
          (pTail j).vertex k = (p j.succ).vertex k := by
        dsimp only [pTail]
        cases hshift j
        rfl
      let q := (p 0).concat rAligned
      have hsum : (∑ j : Fin (n + 2), d j) =
          d 0 + (∑ j : Fin (n + 1), dTail j) := by
        simp only [dTail, Fin.sum_univ_succ]
      rw [hsum]
      refine ⟨q, ?_, ?_, ?_⟩
      · change pathWeight ω ((p 0).concat rAligned) = _
        rw [pathWeight_concat]
        rw [hrWeightAligned, hrWeight]
        rw [Fin.sum_univ_succ (fun j => pathWeight ω (p j))]
        congr 1
      · calc
          q.vertex (Fin.last ((d 0 + (∑ j : Fin (n + 1), dTail j)).1 +
              (d 0 + (∑ j : Fin (n + 1), dTail j)).2)) =
              u ((0 : Fin (n + 2)).castSucc) +
                (((d 0 + (∑ j : Fin (n + 1), dTail j)).1 : ℤ),
                  ((d 0 + (∑ j : Fin (n + 1), dTail j)).2 : ℤ)) := q.finish
          _ = (u ((0 : Fin (n + 2)).castSucc) +
                (((d 0).1 : ℤ), ((d 0).2 : ℤ))) +
                (((∑ j : Fin (n + 1), dTail j).1 : ℤ),
                  ((∑ j : Fin (n + 1), dTail j).2 : ℤ)) := by
            apply Prod.ext <;>
              simp only [Prod.fst_add, Prod.snd_add, Nat.cast_add, add_assoc]
          _ = rAligned.vertex
              (Fin.last ((∑ j : Fin (n + 1), dTail j).1 +
                (∑ j : Fin (n + 1), dTail j).2)) := rAligned.finish.symm
          _ = r.vertex
              (Fin.last ((∑ j : Fin (n + 1), dTail j).1 +
                (∑ j : Fin (n + 1), dTail j).2)) :=
            hrAlignedVertex (Fin.last ((∑ j : Fin (n + 1), dTail j).1 +
              (∑ j : Fin (n + 1), dTail j).2))
          _ = uTail (Fin.last (n + 1)) := hrEnd
          _ = u (Fin.last (n + 2)) := by congr 1
      · intro i
        by_cases hleft : i.val ≤ (d 0).1 + (d 0).2
        · refine ⟨0, ⟨i.val, by omega⟩, ?_⟩
          have hconcat := (p 0).concat_vertex_left rAligned
            ⟨i.val, by omega⟩
          simpa only using hconcat
        · let k : Fin ((∑ j : Fin (n + 1), dTail j).1 +
              (∑ j : Fin (n + 1), dTail j).2 + 1) :=
              ⟨i.val - ((d 0).1 + (d 0).2), by
                have hi := i.isLt
                change i.val < ((d 0).1 + (∑ j : Fin (n + 1), dTail j).1) +
                  ((d 0).2 + (∑ j : Fin (n + 1), dTail j).2) + 1 at hi
                omega⟩
          obtain ⟨j, kj, hvertex⟩ := hrVertices k
          refine ⟨j.succ, kj, ?_⟩
          have hconcat := (p 0).concat_vertex_right rAligned k
          have hi : i = ⟨(d 0).1 + (d 0).2 + k.val, by
              have hi := i.isLt
              simp only [Prod.fst_add, Prod.snd_add]
              change i.val < ((d 0).1 + (∑ j : Fin (n + 1), dTail j).1) +
                ((d 0).2 + (∑ j : Fin (n + 1), dTail j).2) + 1 at hi
              omega⟩ := by
            apply Fin.ext
            dsimp [k]
            have hi := i.isLt
            change i.val < ((d 0).1 + (∑ j : Fin (n + 1), dTail j).1) +
              ((d 0).2 + (∑ j : Fin (n + 1), dTail j).2) + 1 at hi
            have hk := k.isLt
            change i.val - ((d 0).1 + (d 0).2) <
              (∑ j : Fin (n + 1), dTail j).1 +
                (∑ j : Fin (n + 1), dTail j).2 + 1 at hk
            omega
          rw [hi, hconcat]
          rw [hrAlignedVertex k, hvertex, hpTailVertex j kj]

/-- One actual path joins a nonempty compatible finite chain. Its terminal,
weight, and every vertex are conclusions about that same path. -/
theorem exists_concat_finite (ω : Environment) {B : ℕ} (hB : 1 ≤ B)
    (u : Fin (B + 1) → Lattice) (d : Fin B → ℕ × ℕ)
    (hjoin : ∀ j, u j.succ = u j.castSucc +
      (((d j).1 : ℤ), ((d j).2 : ℤ)))
    (p : ∀ j, Path (u j.castSucc) (d j)) :
    ∃ q : Path (u ((⟨0, by omega⟩ : Fin B).castSucc)) (∑ j : Fin B, d j),
      pathWeight ω q = ∑ j : Fin B, pathWeight ω (p j) ∧
      q.vertex (Fin.last ((∑ j : Fin B, d j).1 + (∑ j : Fin B, d j).2)) =
        u (Fin.last B) ∧
      ∀ i : Fin ((∑ j : Fin B, d j).1 + (∑ j : Fin B, d j).2 + 1),
        ∃ j : Fin B, ∃ k : Fin ((d j).1 + (d j).2 + 1),
          q.vertex i = (p j).vertex k := by
  cases B with
  | zero => omega
  | succ n =>
      exact exists_concat_succ n ω hjoin p

end Path

end LPPDifferentiability

end
