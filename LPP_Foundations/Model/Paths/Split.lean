/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Paths.Geometry
public import LPP_Foundations.Model.Paths.WeightConcat
import Mathlib.Algebra.BigOperators.Fin

/-! Restrict actual paths at a local time, retaining the joining vertex in each
vertex sequence and collecting its weight only in the suffix. -/

@[expose] public section

open scoped BigOperators

namespace LPPDifferentiability
namespace Path

/-- The coordinate displacement from the start to the chosen actual vertex. -/
def splitDisplacement {u : Lattice} {d : ℕ × ℕ} (p : Path u d)
    (k : Fin (d.1 + d.2 + 1)) : ℕ × ℕ :=
  (((p.vertex k).1 - u.1).toNat, ((p.vertex k).2 - u.2).toNat)

/-- The first coordinate difference is nonnegative, so conversion loses nothing. -/
theorem splitDisplacement_fst_cast {u : Lattice} {d : ℕ × ℕ} (p : Path u d)
    (k : Fin (d.1 + d.2 + 1)) :
    ((p.splitDisplacement k).1 : ℤ) = (p.vertex k).1 - u.1 := by
  have h := (p.vertex_mem_Icc k).1.1
  exact Int.toNat_of_nonneg (by omega)

/-- The second coordinate difference is nonnegative, so conversion loses nothing. -/
theorem splitDisplacement_snd_cast {u : Lattice} {d : ℕ × ℕ} (p : Path u d)
    (k : Fin (d.1 + d.2 + 1)) :
    ((p.splitDisplacement k).2 : ℤ) = (p.vertex k).2 - u.2 := by
  have h := (p.vertex_mem_Icc k).1.2
  exact Int.toNat_of_nonneg (by omega)

/-- The displacement coordinates add to the selected local time. -/
theorem splitDisplacement_length {u : Lattice} {d : ℕ × ℕ} (p : Path u d)
    (k : Fin (d.1 + d.2 + 1)) :
    (p.splitDisplacement k).1 + (p.splitDisplacement k).2 = k.val := by
  have h₁ := p.splitDisplacement_fst_cast k
  have h₂ := p.splitDisplacement_snd_cast k
  have hl := p.level k
  omega

/-- The actual split lies in the endpoint rectangle. -/
theorem splitDisplacement_le {u : Lattice} {d : ℕ × ℕ} (p : Path u d)
    (k : Fin (d.1 + d.2 + 1)) : p.splitDisplacement k ≤ d := by
  have h₁ := p.splitDisplacement_fst_cast k
  have h₂ := p.splitDisplacement_snd_cast k
  have hr := (p.vertex_mem_Icc k).2
  have hr₁ := hr.1
  have hr₂ := hr.2
  simp only [Prod.fst_add, Prod.snd_add] at hr₁ hr₂
  constructor <;> omega

/-- The literal displacement recovers the actual vertex, also at negative starts. -/
theorem split_vertex {u : Lattice} {d : ℕ × ℕ} (p : Path u d)
    (k : Fin (d.1 + d.2 + 1)) :
    p.vertex k = u + (((p.splitDisplacement k).1 : ℤ),
      ((p.splitDisplacement k).2 : ℤ)) := by
  have h₁ := p.splitDisplacement_fst_cast k
  have h₂ := p.splitDisplacement_snd_cast k
  apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega

/-- The remaining displacement has the remaining number of steps. -/
theorem suffix_length {u : Lattice} {d : ℕ × ℕ} (p : Path u d)
    (k : Fin (d.1 + d.2 + 1)) :
    (d - p.splitDisplacement k).1 + (d - p.splitDisplacement k).2 =
      d.1 + d.2 - k.val := by
  have hlen := p.splitDisplacement_length k
  have hle := p.splitDisplacement_le k
  have h₁ := hle.1
  have h₂ := hle.2
  simp only [Prod.fst_sub, Prod.snd_sub]
  omega

/-- Prefix and suffix displacements recover the original displacement. -/
theorem splitDisplacement_add_sub {u : Lattice} {d : ℕ × ℕ} (p : Path u d)
    (k : Fin (d.1 + d.2 + 1)) :
    p.splitDisplacement k + (d - p.splitDisplacement k) = d := by
  have hle := p.splitDisplacement_le k
  apply Prod.ext
  · exact Nat.add_sub_of_le hle.1
  · exact Nat.add_sub_of_le hle.2

/-- Restriction of the actual vertex sequence through the split vertex. -/
def prefixPath {u : Lattice} {d : ℕ × ℕ} (p : Path u d)
    (k : Fin (d.1 + d.2 + 1)) : Path u (p.splitDisplacement k) where
  vertex i := p.vertex ⟨i.val, by
    have hi := i.isLt
    have hk := k.isLt
    have hl := p.splitDisplacement_length k
    omega⟩
  start := p.start
  finish := by
    convert p.split_vertex k using 1
    congr 1
    apply Fin.ext
    exact p.splitDisplacement_length k
  step i := by
    have hi : i.val < d.1 + d.2 := by
      have hi := i.isLt
      have hk := k.isLt
      have hl := p.splitDisplacement_length k
      omega
    exact p.step ⟨i.val, hi⟩

/-- The suffix starts at the actual split vertex and reindexes the remaining vertices. -/
def suffix {u : Lattice} {d : ℕ × ℕ} (p : Path u d)
    (k : Fin (d.1 + d.2 + 1)) :
    Path (p.vertex k) (d - p.splitDisplacement k) where
  vertex i := p.vertex ⟨k.val + i.val, by
    have hi := i.isLt
    have hk := k.isLt
    have hl := p.suffix_length k
    omega⟩
  start := by
    congr 1
  finish := by
    have hv : (⟨k.val + (Fin.last ((d - p.splitDisplacement k).1 +
        (d - p.splitDisplacement k).2)).val, by
          have hk := k.isLt
          have hl := p.suffix_length k
          simp only [Fin.val_last]
          omega⟩ : Fin (d.1 + d.2 + 1)) = Fin.last (d.1 + d.2) := by
      apply Fin.ext
      have hk := k.isLt
      have hl := p.suffix_length k
      simp only [Fin.val_last]
      omega
    rw [hv, p.finish, p.split_vertex k]
    have hle := p.splitDisplacement_le k
    apply Prod.ext <;>
      simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
        Nat.cast_sub hle.1, Nat.cast_sub hle.2] <;> omega
  step i := by
    have hi : k.val + i.val < d.1 + d.2 := by
      have hi := i.isLt
      have hk := k.isLt
      have hl := p.suffix_length k
      omega
    let j : Fin (d.1 + d.2) := ⟨k.val + i.val, hi⟩
    have hs : (⟨k.val + i.succ.val, by
        simp only [Fin.val_succ]
        omega⟩ : Fin (d.1 + d.2 + 1)) = j.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp only [j]
      omega
    have hc : (⟨k.val + i.castSucc.val, by
        simp only [Fin.val_castSucc]
        omega⟩ : Fin (d.1 + d.2 + 1)) = j.castSucc := rfl
    change p.vertex _ = p.vertex _ + (1, 0) ∨
      p.vertex _ = p.vertex _ + (0, 1)
    rw [hs, hc]
    exact p.step j

/-- The suffix with its equal start written in the form required by concatenation. -/
def suffixForConcat {u : Lattice} {d : ℕ × ℕ} (p : Path u d)
    (k : Fin (d.1 + d.2 + 1)) :
    Path (u + (((p.splitDisplacement k).1 : ℤ), ((p.splitDisplacement k).2 : ℤ)))
      (d - p.splitDisplacement k) where
  vertex := (p.suffix k).vertex
  start := (p.suffix k).start.trans (p.split_vertex k)
  finish := by
    rw [← p.split_vertex k]
    exact (p.suffix k).finish
  step := (p.suffix k).step

/-- Concatenating the restricted sequences recovers every original vertex. -/
theorem concat_prefix_suffix_vertex {u : Lattice} {d : ℕ × ℕ} (p : Path u d)
    (k : Fin (d.1 + d.2 + 1))
    (i : Fin ((p.splitDisplacement k + (d - p.splitDisplacement k)).1 +
      (p.splitDisplacement k + (d - p.splitDisplacement k)).2 + 1)) :
    ((p.prefixPath k).concat (p.suffixForConcat k)).vertex i =
      p.vertex ⟨i.val, by
        have hi := i.isLt
        have he := congrArg (fun e : ℕ × ℕ => e.1 + e.2)
          (p.splitDisplacement_add_sub k)
        omega⟩ := by
  change concatVertex (p.prefixPath k) (p.suffixForConcat k) i = _
  unfold concatVertex
  split_ifs with h
  · rfl
  · change p.vertex _ = p.vertex _
    congr 1
    apply Fin.ext
    have hl := p.splitDisplacement_length k
    dsimp only
    omega

end Path

/-- Splitting an actual path counts the split weight only in its suffix. -/
theorem pathWeight_split (ω : Environment) {u : Lattice} {d : ℕ × ℕ}
    (p : Path u d) (k : Fin (d.1 + d.2 + 1)) :
    pathWeight ω p = pathWeight ω (p.prefixPath k) + pathWeight ω (p.suffix k) := by
  have hweight : pathWeight ω ((p.prefixPath k).concat (p.suffixForConcat k)) =
      pathWeight ω p := by
    have hlen : (p.splitDisplacement k + (d - p.splitDisplacement k)).1 +
        (p.splitDisplacement k + (d - p.splitDisplacement k)).2 = d.1 + d.2 := by
      rw [p.splitDisplacement_add_sub k]
    unfold pathWeight
    rw [← Fin.sum_congr' _ hlen.symm]
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg ω (p.concat_prefix_suffix_vertex k ⟨i.val, by
      have hi := i.isLt
      omega⟩)
  rw [← hweight, pathWeight_concat]
  rfl

end LPPDifferentiability
