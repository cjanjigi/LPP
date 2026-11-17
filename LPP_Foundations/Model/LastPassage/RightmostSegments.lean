/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LPP_Foundations.Model.LastPassage.OptimalSplit
import Mathlib.Tactic

/-! Finite rightmost maximizers retain their order on both actual segments. -/

@[expose] public section
open LPPDifferentiability

namespace LPPDifferentiability

private theorem transport_weight (ω : Environment) {u : Lattice} {a b : ℕ × ℕ}
    (h : a = b) (r : Path u a) : pathWeight ω (h ▸ r) = pathWeight ω r := by
  cases h
  rfl

private theorem transport_vertex {u : Lattice} {a b : ℕ × ℕ}
    (h : a = b) (r : Path u a) (i : Fin (a.1 + a.2 + 1)) :
    (h ▸ r).vertex ⟨i.val, by rw [← h]; exact i.isLt⟩ = r.vertex i := by
  cases h
  rfl

/-- Both actual segments of a greatest maximizing path are greatest maximizers.
The splice argument applies to signed weights and every split vertex. -/
theorem Path.rightmost_maximizing_segments
    (ω : Environment) {u : Lattice} {d : ℕ × ℕ} (p : Path u d)
    (hp : pathWeight ω p = lastPassage ω u d)
    (hgreat : ∀ q : Path u d, pathWeight ω q = lastPassage ω u d →
      ∀ i : Fin (d.1 + d.2 + 1), (q.vertex i).1 ≤ (p.vertex i).1)
    (k : Fin (d.1 + d.2 + 1)) :
    (pathWeight ω (p.prefixPath k) = lastPassage ω u (p.splitDisplacement k) ∧
      ∀ q : Path u (p.splitDisplacement k),
        pathWeight ω q = lastPassage ω u (p.splitDisplacement k) →
        ∀ i : Fin ((p.splitDisplacement k).1 + (p.splitDisplacement k).2 + 1),
          (q.vertex i).1 ≤ ((p.prefixPath k).vertex i).1) ∧
    (pathWeight ω (p.suffix k) =
        lastPassage ω (p.vertex k) (d - p.splitDisplacement k) ∧
      ∀ q : Path (p.vertex k) (d - p.splitDisplacement k),
        pathWeight ω q = lastPassage ω (p.vertex k) (d - p.splitDisplacement k) →
        ∀ i : Fin ((d - p.splitDisplacement k).1 +
            (d - p.splitDisplacement k).2 + 1),
          (q.vertex i).1 ≤ ((p.suffix k).vertex i).1) := by
  classical
  obtain ⟨hpref, hsuff⟩ := p.maximizing_segments ω hp k
  have hsplit := pathWeight_split ω p k
  have hdisp := p.splitDisplacement_add_sub k
  have hlen := p.splitDisplacement_length k
  have hremain := p.suffix_length k
  constructor
  · refine ⟨hpref, ?_⟩
    intro q hq i
    -- Replace the prefix and retain the original suffix.
    let r := q.concat (p.suffixForConcat k)
    let r' : Path u d := hdisp ▸ r
    have hrweight : pathWeight ω r' = pathWeight ω p := by
      rw [show r' = hdisp ▸ r from rfl, transport_weight, pathWeight_concat]
      change pathWeight ω q + pathWeight ω (p.suffix k) = pathWeight ω p
      rw [hq, ← hpref]
      exact hsplit.symm
    have hrmax : pathWeight ω r' = lastPassage ω u d := hrweight.trans hp
    let j : Fin ((p.splitDisplacement k + (d - p.splitDisplacement k)).1 +
        (p.splitDisplacement k + (d - p.splitDisplacement k)).2 + 1) :=
      ⟨i.val, by have hi := i.isLt; simp only [Prod.fst_add, Prod.snd_add]; omega⟩
    have hcomp := hgreat r' hrmax ⟨j.val, by
      have hj := j.isLt
      have he := congrArg (fun t : ℕ × ℕ => t.1 + t.2) hdisp
      omega⟩
    rw [show r' = hdisp ▸ r from rfl, transport_vertex] at hcomp
    have hj : r.vertex j = q.vertex i := by
      exact Path.concat_vertex_left q (p.suffixForConcat k) i
    rw [hj] at hcomp
    exact hcomp
  · refine ⟨hsuff, ?_⟩
    intro q hq i
    -- Replace the suffix, with its root written as the prefix endpoint.
    let q' : Path (u + (((p.splitDisplacement k).1 : ℤ),
        ((p.splitDisplacement k).2 : ℤ))) (d - p.splitDisplacement k) :=
      { vertex := q.vertex
        start := q.start.trans (p.split_vertex k)
        finish := by rw [← p.split_vertex k]; exact q.finish
        step := q.step }
    let r := (p.prefixPath k).concat q'
    let r' : Path u d := hdisp ▸ r
    have hrweight : pathWeight ω r' = pathWeight ω p := by
      rw [show r' = hdisp ▸ r from rfl, transport_weight, pathWeight_concat]
      change pathWeight ω (p.prefixPath k) + pathWeight ω q = pathWeight ω p
      rw [hq, ← hsuff]
      exact hsplit.symm
    have hrmax : pathWeight ω r' = lastPassage ω u d := hrweight.trans hp
    let j : Fin ((p.splitDisplacement k + (d - p.splitDisplacement k)).1 +
        (p.splitDisplacement k + (d - p.splitDisplacement k)).2 + 1) :=
      ⟨(p.splitDisplacement k).1 + (p.splitDisplacement k).2 + i.val, by
        have hi := i.isLt
        simp only [Prod.fst_add, Prod.snd_add]
        omega⟩
    have hcomp := hgreat r' hrmax ⟨j.val, by
      have hj := j.isLt
      have he := congrArg (fun t : ℕ × ℕ => t.1 + t.2) hdisp
      omega⟩
    rw [show r' = hdisp ▸ r from rfl, transport_vertex] at hcomp
    have hj : r.vertex j = q.vertex i := by
      exact Path.concat_vertex_right (p.prefixPath k) q' i
    rw [hj] at hcomp
    simpa only [Path.suffix, j, hlen] using hcomp

end LPPDifferentiability
