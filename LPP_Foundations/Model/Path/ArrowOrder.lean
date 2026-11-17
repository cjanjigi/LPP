/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.Paths.TransverseMerge
import Mathlib.Logic.Function.Iterate
import Lean.Elab.Tactic.Omega

/-! Same-arrow endpoint order for finite up-right trajectories. -/

@[expose] public section

namespace LPPDifferentiability

private theorem iterate_coordinates (s : Lattice → Lattice)
    (hs : ∀ z, s z = z + (1, 0) ∨ s z = z + (0, 1)) (u : Lattice) (n : ℕ) :
    u.1 ≤ (s^[n] u).1 ∧ u.2 ≤ (s^[n] u).2 ∧
      (s^[n] u).1 + (s^[n] u).2 = u.1 + u.2 + (n : ℤ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    rcases hs (s^[n] u) with h | h <;>
      rw [h] <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega

private theorem exists_iterate_path (s : Lattice → Lattice)
    (hs : ∀ z, s z = z + (1, 0) ∨ s z = z + (0, 1)) (u : Lattice) (n : ℕ) :
    ∃ (d : ℕ × ℕ) (p : Path u d), d.1 + d.2 = n ∧
      ∀ (j : ℕ) (hj : j < d.1 + d.2 + 1), p.vertex ⟨j, hj⟩ = s^[j] u := by
  have hc := iterate_coordinates s hs u n
  let a : ℕ := ((s^[n] u).1 - u.1).toNat
  let b : ℕ := ((s^[n] u).2 - u.2).toNat
  have ha : (a : ℤ) = (s^[n] u).1 - u.1 := Int.toNat_of_nonneg (by omega)
  have hb : (b : ℤ) = (s^[n] u).2 - u.2 := Int.toNat_of_nonneg (by omega)
  have hlen : a + b = n := by omega
  let p : Path u (a, b) :=
    { vertex := fun i => s^[i.val] u
      start := by simp
      finish := by
        simp only [Fin.val_last, hlen]
        apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega
      step := by
        intro i
        simp only [Fin.val_succ, Fin.val_castSucc, Function.iterate_succ_apply']
        exact hs (s^[i.val] u) }
  refine ⟨(a, b), p, hlen, ?_⟩
  intro j hj
  rfl

private theorem iterate_children_order (s : Lattice → Lattice)
    (hs : ∀ z, s z = z + (1, 0) ∨ s z = z + (0, 1)) (x : Lattice) (n : ℕ) :
    (s^[n] (x + (0, 1))).1 ≤ (s^[n] (x + (1, 0))).1 := by
  by_contra hn
  have hreverse : (s^[n] (x + (1, 0))).1 < (s^[n] (x + (0, 1))).1 := by omega
  obtain ⟨d, p, hd, hp⟩ := exists_iterate_path s hs (x + (1, 0)) n
  obtain ⟨e, q, he, hq⟩ := exists_iterate_path s hs (x + (0, 1)) n
  have hendp := p.finish
  have hendq := q.finish
  have hpd := hp n (by omega)
  have hqe := hq n (by omega)
  have hpend : s^[n] (x + (1, 0)) = (x + (1, 0)) + ((d.1 : ℤ), (d.2 : ℤ)) := by
    rw [← hpd]
    convert hendp using 1; congr 1; apply Fin.ext; simp only [Fin.val_last]; omega
  have hqend : s^[n] (x + (0, 1)) = (x + (0, 1)) + ((e.1 : ℤ), (e.2 : ℤ)) := by
    rw [← hqe]
    convert hendq using 1; congr 1; apply Fin.ext; simp only [Fin.val_last]; omega
  have hstart : (1 - (0 : ℝ)) * (((x + (0, 1)).1 : ℤ) : ℝ) -
      0 * (((x + (0, 1)).2 : ℤ) : ℝ) <
      (1 - 0) * (((x + (1, 0)).1 : ℤ) : ℝ) - 0 * (((x + (1, 0)).2 : ℤ) : ℝ) := by
    simp only [sub_zero, one_mul, zero_mul, Prod.fst_add, Prod.snd_add]
    exact_mod_cast (show x.1 + 0 < x.1 + 1 by omega)
  have hfinish : (1 - (0 : ℝ)) * ((((x + (1, 0)).1 + d.1 : ℤ)) : ℝ) -
      0 * ((((x + (1, 0)).2 + d.2 : ℤ)) : ℝ) <
      (1 - 0) * ((((x + (0, 1)).1 + e.1 : ℤ)) : ℝ) -
      0 * ((((x + (0, 1)).2 + e.2 : ℤ)) : ℝ) := by
    simp only [sub_zero, one_mul, zero_mul]
    rw [hpend, hqend] at hreverse
    simp only [Prod.fst_add] at hreverse
    exact_mod_cast hreverse
  obtain ⟨j, hj, _, hmeet⟩ := admissible_paths_merge 0 (x + (1, 0)) (x + (0, 1)) d e p q
    (by simp only [Prod.fst_add, Prod.snd_add]; omega) (by omega) hstart hfinish
  have hiter : s^[j] (x + (1, 0)) = s^[j] (x + (0, 1)) := by
    rw [← hp j (by omega), ← hq j (by omega)]
    exact hmeet
  have hsame : s^[n] (x + (1, 0)) = s^[n] (x + (0, 1)) := by
    have hn : n - j + j = n := by omega
    rw [← hn, Function.iterate_add_apply, Function.iterate_add_apply, hiter]
  rw [hsame] at hreverse
  exact (lt_irrefl _) hreverse

/-- Following the same up-right arrow map from a site and its two neighbors
orders their endpoints at the same level. This is the finite planarity and
coalescence step in JR arXiv:1810.03580v3, Appendix A.1, Corollary A.1(a). -/
theorem iterate_arrow_endpoint_sandwich (s : Lattice → Lattice)
    (hs : ∀ z, s z = z + (1, 0) ∨ s z = z + (0, 1)) (x : Lattice) (N : ℕ) :
    (s^[N] (x + (0, 1))).1 ≤ (s^[N + 1] x).1 ∧
      (s^[N + 1] x).1 ≤ (s^[N] (x + (1, 0))).1 := by
  have horder := iterate_children_order s hs x N
  rw [Function.iterate_succ_apply]
  rcases hs x with h | h <;> rw [h] <;> exact ⟨by omega, by omega⟩

/-- Every finite arrow trajectory has an actual up-right path whose vertices
are exactly its iterates, including the initial and terminal sites. This is
Appendix A.1 of JR arXiv:1810.03580v3. -/
theorem exists_arrow_iterate_path_trace (s : Lattice → Lattice)
    (hs : ∀ z, s z = z + (1, 0) ∨ s z = z + (0, 1))
    (x : Lattice) (N : ℕ) :
    ∃ q : Sigma (fun k : Fin (N + 1) => Path x (k.val, N - k.val)),
      ∀ j : ℕ, ∀ hj : j < q.1.val + (N - q.1.val) + 1,
        q.2.vertex ⟨j, hj⟩ = s^[j] x := by
  obtain ⟨⟨d₁, d₂⟩, p, hlength, htrace⟩ := exists_iterate_path s hs x N
  have hd₁ : d₁ ≤ N := by omega
  have hd₂ : d₂ = N - d₁ := by omega
  subst d₂
  let k : Fin (N + 1) := ⟨d₁, Nat.lt_succ_of_le hd₁⟩
  refine ⟨⟨k, p⟩, ?_⟩
  intro j hj
  dsimp only [k] at hj ⊢
  exact htrace j hj

/-- At a fixed horizon, the endpoint-indexed path whose vertices are the
iterates of an arrow map is unique, as in JR arXiv:1810.03580v3, Appendix A.1. -/
theorem exists_unique_arrow_iterate_path_trace (s : Lattice → Lattice)
    (hs : ∀ z, s z = z + (1, 0) ∨ s z = z + (0, 1))
    (x : Lattice) (N : ℕ) :
    ∃! q : Sigma (fun k : Fin (N + 1) => Path x (k.val, N - k.val)),
      ∀ j : ℕ, ∀ hj : j < q.1.val + (N - q.1.val) + 1,
        q.2.vertex ⟨j, hj⟩ = s^[j] x := by
  obtain ⟨q, hqTrace⟩ := exists_arrow_iterate_path_trace s hs x N
  refine ⟨q, hqTrace, ?_⟩
  intro q' hq'Trace
  rcases q with ⟨k, p⟩
  rcases q' with ⟨l, r⟩
  change (∀ j : ℕ, ∀ hj : j < k.val + (N - k.val) + 1,
    p.vertex ⟨j, hj⟩ = s^[j] x) at hqTrace
  change (∀ j : ℕ, ∀ hj : j < l.val + (N - l.val) + 1,
    r.vertex ⟨j, hj⟩ = s^[j] x) at hq'Trace
  have terminalFirst (m : Fin (N + 1)) (path : Path x (m.val, N - m.val))
      (htrace : ∀ j : ℕ, ∀ hj : j < m.val + (N - m.val) + 1,
        path.vertex ⟨j, hj⟩ = s^[j] x) :
      (s^[N] x).1 = x.1 + (m.val : ℤ) := by
    have htraceN := htrace N (by omega)
    have hindex : (⟨N, by omega⟩ : Fin (m.val + (N - m.val) + 1)) =
        Fin.last (m.val + (N - m.val)) := by
      apply Fin.ext
      simp only [Fin.val_last]
      omega
    have hfinish : path.vertex ⟨N, by omega⟩ =
        x + ((m.val : ℤ), ((N - m.val : ℕ) : ℤ)) := by
      rw [hindex]
      exact path.finish
    have htraceFst := congrArg Prod.fst htraceN
    have hfinishFst := congrArg Prod.fst hfinish
    simpa only [Prod.fst_add] using htraceFst.symm.trans hfinishFst
  have hkEnd := terminalFirst k p hqTrace
  have hlEnd := terminalFirst l r hq'Trace
  have hval : k.val = l.val := by
    have hcast : (k.val : ℤ) = (l.val : ℤ) := by omega
    exact_mod_cast hcast
  have hindex : k = l := Fin.ext hval
  subst l
  have hvertices : p.vertex = r.vertex := by
    funext i
    have hp := hqTrace i.val i.isLt
    have hr := hq'Trace i.val i.isLt
    calc
      p.vertex i = p.vertex ⟨i.val, i.isLt⟩ := by congr 1
      _ = s^[i.val] x := hp
      _ = r.vertex ⟨i.val, i.isLt⟩ := hr.symm
      _ = r.vertex i := by congr 1
  have hpath : p = r := by
    cases p
    cases r
    cases hvertices
    rfl
  cases hpath
  rfl

end LPPDifferentiability
