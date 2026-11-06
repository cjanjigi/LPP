/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.LastPassage.Axes
public import LPP_Foundations.Model.LastPassage.Basic
public import LPP_Foundations.Model.Paths.Split
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Deterministic inclusive passage times: the last passage time plus the weight of
the endpoint. Source: Martin (2004), Section 2, whose paths contain their starting point and omit
the final point. -/

@[expose] public section

open scoped BigOperators

namespace LPPDifferentiability

/-- The inclusive passage time from `u` to `u + d`: the last passage time plus the
weight of the endpoint. It is the maximum over paths from `u` to `u + d` of the sum of
all vertex weights, the endpoint included. -/
noncomputable def inclusivePassage (ω : Environment) (u : Lattice) (d : ℕ × ℕ) : ℝ :=
  lastPassage ω u d + ω (u + ((d.1 : ℤ), (d.2 : ℤ)))

/-- A path with one horizontal step has weight equal to the weight of its start. -/
theorem lastPassage_horizontal_one (ω : Environment) (v : Lattice) :
    lastPassage ω v (1, 0) = ω v := by
  rw [lastPassage_horizontal]
  simp

/-- A path with one vertical step has weight equal to the weight of its start. -/
theorem lastPassage_vertical_one (ω : Environment) (v : Lattice) :
    lastPassage ω v (0, 1) = ω v := by
  rw [lastPassage_vertical]
  simp

/-- A path whose displacement has coordinate sum one has weight equal to the weight of
its start. -/
private theorem pathWeight_eq_start_of_length_one (ω : Environment) {v : Lattice}
    {f : ℕ × ℕ} (q : Path v f) (hf : f.1 + f.2 = 1) :
    pathWeight ω q = ω v := by
  obtain ⟨a, b⟩ := f
  rcases (show (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) by
      have h : a + b = 1 := hf
      omega) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [pathWeight_horizontal]
    simp
  · rw [pathWeight_vertical]
    simp

/-- Weights of paths are nonnegative when the weights are. -/
private theorem pathWeight_nonneg {ω : Environment} (hω : ∀ z, 0 ≤ ω z) {u : Lattice}
    {d : ℕ × ℕ} (q : Path u d) : 0 ≤ pathWeight ω q := by
  unfold pathWeight
  exact Finset.sum_nonneg fun i _ => hω _

/-- Transport a bound on a path whose displacement equals `f` to the last passage time
for `f`. -/
private theorem pathWeight_le_lastPassage_of_eq {ω : Environment} {u : Lattice}
    {e f : ℕ × ℕ} (h : e = f) (q : Path u e) :
    pathWeight ω q ≤ lastPassage ω u f := by
  subst h
  exact pathWeight_le_lastPassage ω q

/-- Upper bound for the corner step. A maximizing path to `u + d` whose last step ends
at a neighbour `u + e` has weight at most the inclusive passage time to `e`. -/
private theorem pathWeight_le_inclusivePassage_of_split {ω : Environment} {u : Lattice}
    {d e : ℕ × ℕ} (p : Path u d) (k : Fin (d.1 + d.2 + 1)) (hk : k.val + 1 = d.1 + d.2)
    (he : p.splitDisplacement k = e) :
    pathWeight ω p ≤ inclusivePassage ω u e := by
  have hf : (d - p.splitDisplacement k).1 + (d - p.splitDisplacement k).2 = 1 := by
    have h := p.suffix_length k
    omega
  have hprefix : pathWeight ω (p.prefixPath k) ≤ lastPassage ω u e :=
    pathWeight_le_lastPassage_of_eq he (p.prefixPath k)
  have hvertex : p.vertex k = u + ((e.1 : ℤ), (e.2 : ℤ)) := by
    rw [p.split_vertex k, he]
  rw [pathWeight_split ω p k, pathWeight_eq_start_of_length_one ω (p.suffix k) hf,
    inclusivePassage, hvertex]
  linarith

/-- Corner recursion. The last passage time to the corner `u + (d1 + 1, d2 + 1)` is the
larger of the two inclusive passage times to its neighbours `u + (d1, d2 + 1)` and
`u + (d1 + 1, d2)`. The last vertex before the endpoint is one of these two neighbours. -/
theorem lastPassage_succ_succ (ω : Environment) (u : Lattice) (d : ℕ × ℕ) :
    lastPassage ω u (d.1 + 1, d.2 + 1) =
      max (inclusivePassage ω u (d.1, d.2 + 1)) (inclusivePassage ω u (d.1 + 1, d.2)) := by
  apply le_antisymm
  · -- Upper bound: split a maximizing path one step before its end.
    obtain ⟨p, hp⟩ := exists_pathWeight_eq_lastPassage ω u (d.1 + 1, d.2 + 1)
    rw [← hp]
    let k : Fin ((d.1 + 1, d.2 + 1).1 + (d.1 + 1, d.2 + 1).2 + 1) :=
      ⟨d.1 + d.2 + 1, by
        show d.1 + d.2 + 1 < (d.1 + 1) + (d.2 + 1) + 1
        omega⟩
    have hk : k.val + 1 = (d.1 + 1, d.2 + 1).1 + (d.1 + 1, d.2 + 1).2 := by
      show d.1 + d.2 + 1 + 1 = (d.1 + 1) + (d.2 + 1)
      omega
    have hlen : (p.splitDisplacement k).1 + (p.splitDisplacement k).2 = d.1 + d.2 + 1 :=
      p.splitDisplacement_length k
    have hle : (p.splitDisplacement k).1 ≤ d.1 + 1 ∧ (p.splitDisplacement k).2 ≤ d.2 + 1 :=
      p.splitDisplacement_le k
    rcases (show (p.splitDisplacement k = (d.1, d.2 + 1)) ∨
        (p.splitDisplacement k = (d.1 + 1, d.2)) by
      obtain ⟨h1, h2⟩ := hle
      rcases (show ((p.splitDisplacement k).1 = d.1 ∧ (p.splitDisplacement k).2 = d.2 + 1) ∨
          ((p.splitDisplacement k).1 = d.1 + 1 ∧ (p.splitDisplacement k).2 = d.2) by
        omega) with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · exact Or.inl (Prod.ext h3 h4)
      · exact Or.inr (Prod.ext h3 h4)) with he | he
    · exact le_max_of_le_left
        (pathWeight_le_inclusivePassage_of_split p k hk he)
    · exact le_max_of_le_right
        (pathWeight_le_inclusivePassage_of_split p k hk he)
  · -- Lower bound: extend a maximizing path to a neighbour by one step.
    apply max_le
    · have hs := lastPassage_superadditive ω u (d.1, d.2 + 1) (1, 0)
      rw [lastPassage_horizontal_one] at hs
      have hd : (d.1, d.2 + 1) + (1, 0) = (d.1 + 1, d.2 + 1) := by
        ext <;> simp
      rw [hd] at hs
      unfold inclusivePassage
      exact hs
    · have hs := lastPassage_superadditive ω u (d.1 + 1, d.2) (0, 1)
      rw [lastPassage_vertical_one] at hs
      have hd : (d.1 + 1, d.2) + (0, 1) = (d.1 + 1, d.2 + 1) := by
        ext <;> simp
      rw [hd] at hs
      unfold inclusivePassage
      exact hs

/-- The inclusive passage time along a horizontal segment is the sum of its `n + 1`
weights: the `n` weights before the endpoint and the endpoint itself. -/
theorem inclusivePassage_horizontal (ω : Environment) (u : Lattice) (n : ℕ) :
    inclusivePassage ω u (n, 0) = ∑ i : Fin (n + 1), ω (u.1 + (i.val : ℤ), u.2) := by
  unfold inclusivePassage
  rw [lastPassage_horizontal, Fin.sum_univ_castSucc]
  congr 1
  congr 1
  ext <;> simp

/-- The inclusive passage time along a vertical segment is the sum of its `n + 1`
weights: the `n` weights before the endpoint and the endpoint itself. -/
theorem inclusivePassage_vertical (ω : Environment) (u : Lattice) (n : ℕ) :
    inclusivePassage ω u (0, n) = ∑ j : Fin (n + 1), ω (u.1, u.2 + (j.val : ℤ)) := by
  unfold inclusivePassage
  rw [lastPassage_vertical, Fin.sum_univ_castSucc]
  congr 1
  congr 1
  ext <;> simp

/-- With nonnegative weights, starting earlier never lowers the inclusive passage time to
the same endpoint. The path from the earlier start may be prefixed by any path from `u`
to `u + a`, which only adds nonnegative weight. -/
theorem inclusivePassage_le_of_earlier_start {ω : Environment} (hω : ∀ z, 0 ≤ ω z)
    (u : Lattice) (a d : ℕ × ℕ) :
    inclusivePassage ω (u + ((a.1 : ℤ), (a.2 : ℤ))) d ≤ inclusivePassage ω u (a + d) := by
  have hlast : lastPassage ω (u + ((a.1 : ℤ), (a.2 : ℤ))) d ≤ lastPassage ω u (a + d) := by
    obtain ⟨p, hp⟩ := exists_pathWeight_eq_lastPassage ω (u + ((a.1 : ℤ), (a.2 : ℤ))) d
    obtain ⟨q⟩ := pathNonempty u a
    rw [← hp]
    have hprefix : 0 ≤ pathWeight ω q := pathWeight_nonneg hω q
    calc
      pathWeight ω p ≤ pathWeight ω q + pathWeight ω p := by linarith
      _ = pathWeight ω (q.concat p) := (pathWeight_concat ω q p).symm
      _ ≤ lastPassage ω u (a + d) := pathWeight_le_lastPassage ω (q.concat p)
  have hend : u + ((a.1 : ℤ), (a.2 : ℤ)) + ((d.1 : ℤ), (d.2 : ℤ)) =
      u + (((a + d).1 : ℤ), ((a + d).2 : ℤ)) := by
    apply Prod.ext
    · simp only [Prod.fst_add, Nat.cast_add]
      ring
    · simp only [Prod.snd_add, Nat.cast_add]
      ring
  unfold inclusivePassage
  rw [hend]
  linarith

end LPPDifferentiability
