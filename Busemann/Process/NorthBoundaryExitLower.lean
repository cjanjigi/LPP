/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.Definitions.Additive
public import Busemann.Frozen.Definitions.Recovery
public import LPP_Foundations.Model.LastPassage.Basic
public import Mathlib.Data.Finset.Lattice.Fold
import Busemann.Process.NorthBoundaryTail
import LPP_Foundations.Model.LastPassage.Bounds
import Lean.Elab.Tactic.Omega

/-! The finite north-boundary exit maximum is bounded by the modified passage value. -/

@[expose] public section

open LPPDifferentiability LPP.Busemann

namespace LPP.Busemann

/-- Under additivity and pointwise recovery, every north-boundary exit value is
at most the modified passage with only the north boundary changed. This is
the lower half of a derived one-sided exit formula related to the exit
decomposition in GRS 1510.00859v2, Lemma 6.4, and the NE passage in (6.8). -/
theorem north_boundary_exit_max_le_lastPassage
    (ω : Environment) (C : Lattice → Lattice → ℝ)
    (hC : is_additive C) (hrec : recovers_environment ω C)
    (x : Lattice) (d : ℕ × ℕ) :
    let v : Lattice := x + ((d.1 : ℤ), (d.2 : ℤ))
    let N : Environment := fun z =>
      if z.2 = v.2 ∧ z.1 < v.1 then C z (z + (1, 0)) else ω z
    (Finset.univ : Finset (Fin (d.1 + 1))).sup' Finset.univ_nonempty
      (fun k => lastPassage ω x (d.1 - k.val, d.2) +
        C (v - ((k.val : ℤ), 0)) v) ≤ lastPassage N x d := by
  classical
  let v : Lattice := x + ((d.1 : ℤ), (d.2 : ℤ))
  let N : Environment := fun z =>
    if z.2 = v.2 ∧ z.1 < v.1 then C z (z + (1, 0)) else ω z
  let objective : Fin (d.1 + 1) → ℝ := fun k =>
    lastPassage ω x (d.1 - k.val, d.2) + C (v - ((k.val : ℤ), 0)) v
  change (Finset.univ : Finset (Fin (d.1 + 1))).sup' Finset.univ_nonempty
    objective ≤ lastPassage N x d
  -- Recovery makes the changed north-boundary weights no smaller.
  have hweight : ∀ z : Lattice, ω z ≤ N z := by
    intro z
    by_cases hrow : z.2 = v.2 ∧ z.1 < v.1
    · have hN : N z = C z (z + (1, 0)) := by simp [N, hrow]
      rw [hN, ← hrec z]
      exact min_le_left _ _
    · have hN : N z = ω z := by simp [N, hrow]
      rw [hN]
  -- Each exit index yields a prefix and its remaining horizontal boundary tail.
  have hobjective (k : Fin (d.1 + 1)) :
      objective k ≤ lastPassage N x d := by
    let e : ℕ × ℕ := (d.1 - k.val, d.2)
    let f : ℕ × ℕ := (k.val, 0)
    have hk_le : k.val ≤ d.1 := by omega
    change lastPassage ω x e + C (v - ((k.val : ℤ), 0)) v ≤
      lastPassage N x d
    -- The natural prefix and horizontal remainder recover the full displacement.
    have hef : e + f = d := by
      apply Prod.ext
      · simp only [e, f, Prod.fst_add]
        exact Nat.sub_add_cancel hk_le
      · simp only [e, f, Prod.snd_add, Nat.add_zero]
    -- The prefix endpoint is exactly the left endpoint of the north-boundary tail.
    have hstart : x + ((e.1 : ℤ), (e.2 : ℤ)) =
        v - ((k.val : ℤ), 0) := by
      apply Prod.ext
      · dsimp only [v, e]
        simp only [Prod.fst_add, Prod.fst_sub]
        rw [Nat.cast_sub hk_le]
        omega
      · dsimp only [v, e]
        simp only [Prod.snd_add, Prod.snd_sub, sub_zero]
    -- The horizontal identity evaluates this actual tail.
    have htail : lastPassage N (x + ((e.1 : ℤ), (e.2 : ℤ))) f =
        C (v - ((k.val : ℤ), 0)) v := by
      rw [hstart]
      dsimp only [f]
      exact north_boundary_horizontal_passage_eq_cocycle ω C hC v k.val
    -- Compare the ordinary prefix using the pointwise recovered-weight bound.
    have hprefix : lastPassage ω x e ≤ lastPassage N x e :=
      lastPassage_mono ω N x e hweight
    -- Concatenating the prefix and tail gives the full modified passage value.
    have hsuper : lastPassage N x e +
        lastPassage N (x + ((e.1 : ℤ), (e.2 : ℤ))) f ≤ lastPassage N x d := by
      calc
        lastPassage N x e +
            lastPassage N (x + ((e.1 : ℤ), (e.2 : ℤ))) f ≤
              lastPassage N x (e + f) := lastPassage_superadditive N x e f
        _ = lastPassage N x d := by rw [hef]
    calc
      lastPassage ω x e + C (v - ((k.val : ℤ), 0)) v =
          lastPassage ω x e +
            lastPassage N (x + ((e.1 : ℤ), (e.2 : ℤ))) f := by rw [← htail]
      _ ≤ lastPassage N x e +
          lastPassage N (x + ((e.1 : ℤ), (e.2 : ℤ))) f := add_le_add hprefix le_rfl
      _ ≤ lastPassage N x d := hsuper
  -- Apply the finite-supremum order property to all literal exit indices.
  rw [Finset.sup'_le_iff]
  intro k _
  exact hobjective k

end LPP.Busemann
