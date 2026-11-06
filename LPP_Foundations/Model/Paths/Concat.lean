/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.Path
import Lean.Elab.Tactic.Omega

/-! Concatenation on the finite path carrier, including empty pieces. -/

@[expose] public section

namespace LPPDifferentiability

namespace Path

/-- The joined vertex sequence, using the second piece at the joining index. -/
def concatVertex {u : Lattice} {d e : ℕ × ℕ} (p : Path u d)
    (q : Path (u + ((d.1 : ℤ), (d.2 : ℤ))) e)
    (i : Fin ((d + e).1 + (d + e).2 + 1)) : Lattice :=
  if h : i.val < d.1 + d.2 then
    p.vertex ⟨i.val, by omega⟩
  else
    q.vertex ⟨i.val - (d.1 + d.2), by
      have hi := i.isLt
      simp only [Prod.fst_add, Prod.snd_add] at hi
      omega⟩

theorem concatVertex_left {u : Lattice} {d e : ℕ × ℕ} (p : Path u d)
    (q : Path (u + ((d.1 : ℤ), (d.2 : ℤ))) e)
    (i : Fin (d.1 + d.2 + 1)) :
    concatVertex p q ⟨i.val, by
      have hi := i.isLt
      simp only [Prod.fst_add, Prod.snd_add]
      omega⟩ = p.vertex i := by
  dsimp only [concatVertex]
  split_ifs with h
  · rfl
  · have hi : i.val = d.1 + d.2 := by omega
    have he : i = Fin.last (d.1 + d.2) := Fin.ext hi
    subst i
    simp only [Fin.val_last, Nat.sub_self]
    exact q.start.trans p.finish.symm

theorem concatVertex_right {u : Lattice} {d e : ℕ × ℕ} (p : Path u d)
    (q : Path (u + ((d.1 : ℤ), (d.2 : ℤ))) e)
    (i : Fin (e.1 + e.2 + 1)) :
    concatVertex p q ⟨d.1 + d.2 + i.val, by
      have hi := i.isLt
      simp only [Prod.fst_add, Prod.snd_add]
      omega⟩ = q.vertex i := by
  dsimp only [concatVertex]
  rw [dite_eq_right (by omega)]
  congr 1
  apply Fin.ext
  exact Nat.add_sub_cancel_left _ _

/-- Join paths at their common endpoint, retaining that vertex once. -/
def concat {u : Lattice} {d e : ℕ × ℕ} (p : Path u d)
    (q : Path (u + ((d.1 : ℤ), (d.2 : ℤ))) e) : Path u (d + e) where
  vertex := concatVertex p q
  start := (concatVertex_left p q 0).trans p.start
  finish := by
    calc
      concatVertex p q (Fin.last ((d + e).1 + (d + e).2)) =
          q.vertex (Fin.last (e.1 + e.2)) := by
        convert concatVertex_right p q (Fin.last (e.1 + e.2)) using 1
        congr 1
        apply Fin.ext
        simp only [Fin.val_last, Prod.fst_add, Prod.snd_add]
        omega
      _ = (u + ((d.1 : ℤ), (d.2 : ℤ))) + ((e.1 : ℤ), (e.2 : ℤ)) := q.finish
      _ = u + (((d + e).1 : ℤ), ((d + e).2 : ℤ)) := by
        apply Prod.ext <;>
          simp only [Prod.fst_add, Prod.snd_add, Nat.cast_add] <;> omega
  step i := by
    by_cases h : i.val < d.1 + d.2
    · have hs := p.step ⟨i.val, h⟩
      have hl : concatVertex p q i.castSucc = p.vertex (⟨i.val, h⟩ : Fin (d.1 + d.2)).castSucc :=
        concatVertex_left p q ⟨i.val, by omega⟩
      have hr : concatVertex p q i.succ = p.vertex (⟨i.val, h⟩ : Fin (d.1 + d.2)).succ :=
        concatVertex_left p q ⟨i.val + 1, by omega⟩
      rw [hl, hr]
      exact hs
    · have hi := i.isLt
      simp only [Prod.fst_add, Prod.snd_add] at hi
      have hj : i.val - (d.1 + d.2) < e.1 + e.2 := by omega
      let j : Fin (e.1 + e.2) := ⟨i.val - (d.1 + d.2), hj⟩
      have hli : i.castSucc =
          (⟨d.1 + d.2 + j.castSucc.val, by
            have hj' := j.isLt
            simp only [Prod.fst_add, Prod.snd_add]
            omega⟩ : Fin ((d + e).1 + (d + e).2 + 1)) := by
        apply Fin.ext
        dsimp only [j]
        simp only [Fin.val_castSucc]
        omega
      have hri : i.succ =
          (⟨d.1 + d.2 + j.succ.val, by
            have hj' := j.succ.isLt
            simp only [Prod.fst_add, Prod.snd_add]
            omega⟩ : Fin ((d + e).1 + (d + e).2 + 1)) := by
        apply Fin.ext
        dsimp only [j, Fin.val_succ]
        omega
      rw [hli, hri, concatVertex_right p q j.castSucc,
        concatVertex_right p q j.succ]
      exact q.step j

/-- The first segment includes its terminal vertex as a vertex of the join. -/
theorem concat_vertex_left {u : Lattice} {d e : ℕ × ℕ} (p : Path u d)
    (q : Path (u + ((d.1 : ℤ), (d.2 : ℤ))) e)
    (i : Fin (d.1 + d.2 + 1)) :
    (p.concat q).vertex ⟨i.val, by
      have hi := i.isLt
      simp only [Prod.fst_add, Prod.snd_add]
      omega⟩ = p.vertex i :=
  concatVertex_left p q i

/-- The second segment starts at the joining vertex. -/
theorem concat_vertex_right {u : Lattice} {d e : ℕ × ℕ} (p : Path u d)
    (q : Path (u + ((d.1 : ℤ), (d.2 : ℤ))) e)
    (i : Fin (e.1 + e.2 + 1)) :
    (p.concat q).vertex ⟨d.1 + d.2 + i.val, by
      have hi := i.isLt
      simp only [Prod.fst_add, Prod.snd_add]
      omega⟩ = q.vertex i :=
  concatVertex_right p q i

end Path

end LPPDifferentiability
