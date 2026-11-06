/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.PathWeight

/-! Lattice translations of paths and their collected weights. -/

@[expose] public section

namespace LPPDifferentiability
namespace Path

/-- Paths are determined by their vertex functions. -/
@[ext] theorem ext {u : Lattice} {d : ℕ × ℕ} {p q : Path u d}
    (h : ∀ i, p.vertex i = q.vertex i) : p = q := by
  have hv : p.vertex = q.vertex := funext h
  cases p
  cases q
  cases hv
  rfl

/-- Add an arbitrary integer lattice vector to every vertex. -/
def translate {u : Lattice} {d : ℕ × ℕ} (p : Path u d) (v : Lattice) :
    Path (v + u) d where
  vertex i := v + p.vertex i
  start := by rw [p.start]
  finish := by rw [p.finish, add_assoc]
  step i := by
    rcases p.step i with h | h
    · exact Or.inl (by rw [h, add_assoc])
    · exact Or.inr (by rw [h, add_assoc])

@[simp] theorem translate_vertex {u : Lattice} {d : ℕ × ℕ} (p : Path u d)
    (v : Lattice) (i : Fin (d.1 + d.2 + 1)) :
    (p.translate v).vertex i = v + p.vertex i := rfl

/-- Subtract the translation vector, returning to the original start point. -/
def untranslate (v : Lattice) {u : Lattice} {d : ℕ × ℕ} (p : Path (v + u) d) :
    Path u d where
  vertex i := -v + p.vertex i
  start := by rw [p.start, neg_add_cancel_left]
  finish := by rw [p.finish, add_assoc, neg_add_cancel_left]
  step i := by
    rcases p.step i with h | h
    · exact Or.inl (by rw [h, add_assoc])
    · exact Or.inr (by rw [h, add_assoc])

@[simp] theorem untranslate_vertex (v : Lattice) {u : Lattice} {d : ℕ × ℕ}
    (p : Path (v + u) d) (i : Fin (d.1 + d.2 + 1)) :
    (untranslate v p).vertex i = -v + p.vertex i := rfl

@[simp] theorem untranslate_translate {u : Lattice} {d : ℕ × ℕ}
    (p : Path u d) (v : Lattice) : untranslate v (p.translate v) = p := by
  apply Path.ext
  intro i
  exact neg_add_cancel_left v (p.vertex i)

@[simp] theorem translate_untranslate (v : Lattice) {u : Lattice} {d : ℕ × ℕ}
    (p : Path (v + u) d) : (untranslate v p).translate v = p := by
  apply Path.ext
  intro i
  exact add_neg_cancel_left v (p.vertex i)

/-- Translation is a bijection on the paths with a fixed displacement. -/
def translateEquiv (v u : Lattice) (d : ℕ × ℕ) : Path u d ≃ Path (v + u) d where
  toFun p := p.translate v
  invFun p := untranslate v p
  left_inv p := untranslate_translate p v
  right_inv p := translate_untranslate v p

@[simp] theorem translateEquiv_apply (v u : Lattice) (d : ℕ × ℕ) (p : Path u d) :
    translateEquiv v u d p = p.translate v := rfl

@[simp] theorem translateEquiv_symm_apply (v u : Lattice) (d : ℕ × ℕ)
    (p : Path (v + u) d) : (translateEquiv v u d).symm p = untranslate v p := rfl

end Path

/-- Translating a path is equivalent to translating the environment in its weight. -/
theorem pathWeight_translate (ω : Environment) {u : Lattice} {d : ℕ × ℕ}
    (p : Path u d) (v : Lattice) :
    pathWeight ω (p.translate v) = pathWeight (fun z => ω (v + z)) p := rfl

end LPPDifferentiability
