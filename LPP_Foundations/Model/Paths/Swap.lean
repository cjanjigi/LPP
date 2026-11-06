/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Paths.Translate
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Coordinate transposition of the actual finite up-right paths. -/

@[expose] public section

open scoped BigOperators

namespace LPPDifferentiability

private theorem finCast_succ {m n : ℕ} (h : m = n) (i : Fin m) :
    Fin.cast (congrArg Nat.succ h) i.succ = (Fin.cast h i).succ := by
  apply Fin.ext
  rfl

private theorem finCast_castSucc {m n : ℕ} (h : m = n) (i : Fin m) :
    Fin.cast (congrArg Nat.succ h) i.castSucc = (Fin.cast h i).castSucc := by
  apply Fin.ext
  rfl

namespace Path

/-- Swap the two coordinates of every vertex, reindexing by the equal total path length. -/
def swap {u : Lattice} {d : ℕ × ℕ} (p : Path u d) : Path u.swap d.swap where
  vertex i :=
    (p.vertex (Fin.cast (congrArg Nat.succ (Nat.add_comm d.2 d.1)) i)).swap
  start := by
    change (p.vertex (Fin.cast (congrArg Nat.succ (Nat.add_comm d.2 d.1))
      (0 : Fin (d.2 + d.1 + 1)))).swap = u.swap
    rw [show Fin.cast (congrArg Nat.succ (Nat.add_comm d.2 d.1))
      (0 : Fin (d.2 + d.1 + 1)) = 0 by
        apply Fin.ext
        rfl]
    rw [p.start]
  finish := by
    change (p.vertex (Fin.cast (congrArg Nat.succ (Nat.add_comm d.2 d.1))
      (Fin.last (d.2 + d.1)))).swap = _
    rw [show Fin.cast (congrArg Nat.succ (Nat.add_comm d.2 d.1))
      (Fin.last (d.2 + d.1)) = Fin.last (d.1 + d.2) by
        apply Fin.ext
        simp only [Fin.val_cast, Fin.val_last]
        exact Nat.add_comm d.2 d.1]
    rw [p.finish]
    simp [Prod.swap]
  step i := by
    let h : d.2 + d.1 = d.1 + d.2 := Nat.add_comm d.2 d.1
    have hstep := p.step (Fin.cast h i)
    have hsucc := finCast_succ h i
    have hcastSucc := finCast_castSucc h i
    change (p.vertex (Fin.cast (congrArg Nat.succ h) i.succ)).swap =
      (p.vertex (Fin.cast (congrArg Nat.succ h) i.castSucc)).swap + (1, 0) ∨
      (p.vertex (Fin.cast (congrArg Nat.succ h) i.succ)).swap =
      (p.vertex (Fin.cast (congrArg Nat.succ h) i.castSucc)).swap + (0, 1)
    rw [hsucc, hcastSucc]
    rcases hstep with hstep | hstep
    · right
      rw [hstep]
      simp [Prod.swap]
    · left
      rw [hstep]
      simp [Prod.swap]

@[simp] theorem swap_vertex {u : Lattice} {d : ℕ × ℕ} (p : Path u d)
    (i : Fin (d.2 + d.1 + 1)) :
    (p.swap).vertex i =
      (p.vertex (Fin.cast (congrArg Nat.succ (Nat.add_comm d.2 d.1)) i)).swap := rfl

/-- The vertex formula written with an index in the original path's order. -/
theorem swap_vertex_cast {u : Lattice} {d : ℕ × ℕ} (p : Path u d)
    (i : Fin (d.1 + d.2 + 1)) :
    (p.swap).vertex (Fin.cast (congrArg Nat.succ (Nat.add_comm d.1 d.2)) i) =
      (p.vertex i).swap := by
  rw [swap_vertex]
  have hindex :
      Fin.cast (congrArg Nat.succ (Nat.add_comm d.2 d.1))
        (Fin.cast (congrArg Nat.succ (Nat.add_comm d.1 d.2)) i) = i := by
    apply Fin.ext
    rfl
  rw [hindex]

/-- Swapping the actual path twice returns the original path. -/
@[simp] theorem swap_swap {u : Lattice} {d : ℕ × ℕ} (p : Path u d) :
    p.swap.swap = p := by
  apply Path.ext
  intro i
  simp only [swap_vertex, Prod.swap_swap]
  have hindex :
      Fin.cast (congrArg Nat.succ (Nat.add_comm d.2 d.1))
        (Fin.cast (congrArg Nat.succ (Nat.add_comm d.1 d.2)) i) = i := by
    apply Fin.ext
    rfl
  rw [hindex]

end Path

/-- Coordinate transposition preserves each path's terminal-excluded weight when
the site field is transposed at the same time. -/
theorem pathWeight_swap (ω : Environment) {u : Lattice} {d : ℕ × ℕ}
    (p : Path u d) :
    pathWeight ω p.swap = pathWeight (fun z => ω z.swap) p := by
  let h : d.1 + d.2 = d.2 + d.1 := Nat.add_comm d.1 d.2
  let e : Fin (d.1 + d.2) ≃ Fin (d.2 + d.1) := {
    toFun := fun i => Fin.cast h i
    invFun := fun i => Fin.cast h.symm i
    left_inv := by
      intro i
      apply Fin.ext
      rfl
    right_inv := by
      intro i
      apply Fin.ext
      rfl
  }
  have hvertex (i : Fin (d.1 + d.2)) :
      (p.swap).vertex (e i).castSucc = (p.vertex i.castSucc).swap := by
    change (p.swap).vertex (Fin.cast h i).castSucc = (p.vertex i.castSucc).swap
    rw [Path.swap_vertex]
    have hindex :
        Fin.cast (congrArg Nat.succ h.symm) ((Fin.cast h i).castSucc) = i.castSucc := by
      apply Fin.ext
      rfl
    rw [hindex]
  unfold pathWeight
  calc
    (∑ i : Fin (d.2 + d.1), ω ((p.swap).vertex i.castSucc)) =
        ∑ i : Fin (d.1 + d.2), ω ((p.swap).vertex (e i).castSucc) :=
      (Equiv.sum_comp e (fun i => ω ((p.swap).vertex i.castSucc))).symm
    _ = ∑ i : Fin (d.1 + d.2), ω ((p.vertex i.castSucc).swap) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hvertex]
    _ = ∑ i : Fin (d.1 + d.2), (fun z => ω z.swap) (p.vertex i.castSucc) := by
      apply Finset.sum_congr rfl
      intro i _
      rfl

end LPPDifferentiability
