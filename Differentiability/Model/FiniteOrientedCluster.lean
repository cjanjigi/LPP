/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.Paths.OrientedCompactness
public import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Basic.Finite.Prod
import Lean.Elab.Tactic.Omega

/-!
# Finiteness of the oriented endpoint set

The terminal site of a finite endpoint witness may be bad. Every earlier site
must be good, and the zero-length path is included.
-/

public section

namespace LPPDifferentiability

/-- The level of the vertex at time `i` is exactly `i`. -/
theorem oriented_path_level {n : ℕ} (q : Fin (n + 1) → ℕ × ℕ)
    (hzero : q 0 = (0, 0))
    (hstep : ∀ i : Fin n,
      q i.succ = q i.castSucc + (1, 0) ∨ q i.succ = q i.castSucc + (0, 1))
    (i : Fin (n + 1)) : (q i).1 + (q i).2 = i := by
  have hlevel : ∀ k (hk : k ≤ n),
      (q ⟨k, by omega⟩).1 + (q ⟨k, by omega⟩).2 = k := by
    intro k
    induction k with
    | zero => intro _; simp only [show (⟨0, by omega⟩ : Fin (n + 1)) = 0 from rfl,
        hzero, Nat.add_zero]
    | succ k ih =>
      intro hkn
      have hk : k < n := by omega
      have hp := ih (by omega)
      rcases hstep ⟨k, hk⟩ with hs | hs
      · change q ⟨k + 1, by omega⟩ = q ⟨k, by omega⟩ + (1, 0) at hs
        rw [hs]
        change (q ⟨k, by omega⟩).1 + 1 + ((q ⟨k, by omega⟩).2 + 0) = k + 1
        omega
      · change q ⟨k + 1, by omega⟩ = q ⟨k, by omega⟩ + (0, 1) at hs
        rw [hs]
        change (q ⟨k, by omega⟩).1 + 0 + ((q ⟨k, by omega⟩).2 + 1) = k + 1
        omega
  exact hlevel i (by omega)

/-- A bounded collection of levels in the natural quadrant is finite. -/
theorem finite_quadrant_bounded_levels (n : ℕ) :
    {v : ℕ × ℕ | v.1 + v.2 ≤ n}.Finite := by
  apply ((Set.finite_Iic n).prod (Set.finite_Iic n)).subset
  intro v hv
  change v.1 ≤ n ∧ v.2 ≤ n
  change v.1 + v.2 ≤ n at hv
  omega

/-- If no infinite good oriented path starts at zero, the endpoint set
is finite. Only sites strictly before the endpoint must be good. -/
theorem finite_oriented_endpoint_set (G : Set (ℕ × ℕ))
    (hno : ¬ ∃ v : ℕ → ℕ × ℕ, v 0 = (0, 0) ∧
      (∀ i, v (i + 1) = v i + (1, 0) ∨ v (i + 1) = v i + (0, 1)) ∧
      ∀ i, v i ∈ G) :
    {x : ℕ × ℕ | ∃ n : ℕ, ∃ q : Fin (n + 1) → ℕ × ℕ,
      q 0 = (0, 0) ∧ q (Fin.last n) = x ∧
      (∀ i : Fin n,
        q i.succ = q i.castSucc + (1, 0) ∨ q i.succ = q i.castSucc + (0, 1)) ∧
      ∀ i : Fin (n + 1), (i : ℕ) < n → q i ∈ G}.Finite := by
  classical
  let R : Set (ℕ × ℕ) := {x | ∃ n : ℕ, ∃ q : Fin (n + 1) → ℕ × ℕ,
    q 0 = (0, 0) ∧ q (Fin.last n) = x ∧
    (∀ i : Fin n,
      q i.succ = q i.castSucc + (1, 0) ∨ q i.succ = q i.castSucc + (0, 1)) ∧
    ∀ i : Fin (n + 1), (i : ℕ) < n → q i ∈ G}
  change R.Finite
  by_contra hinfinite
  apply hno
  apply exists_infinite_good_oriented_path G
  intro n
  have hlarge : ∃ x ∈ R, n < x.1 + x.2 := by
    by_contra h
    apply hinfinite
    apply (finite_quadrant_bounded_levels n).subset
    intro x hx
    change x.1 + x.2 ≤ n
    by_contra hnx
    exact h ⟨x, hx, by omega⟩
  obtain ⟨x, ⟨m, q, hzero, hlast, hstep, hgood⟩, hx⟩ := hlarge
  have hlength := oriented_path_level q hzero hstep (Fin.last m)
  rw [hlast] at hlength
  have hnm : n < m := by change x.1 + x.2 = m at hlength; omega
  let p : Fin (n + 1) → ℕ × ℕ := fun i => q ⟨i, by omega⟩
  refine ⟨p, hzero, ?_, ?_⟩
  · intro i
    exact hstep ⟨i, by omega⟩
  · intro i
    exact hgood ⟨i, by omega⟩
      (Nat.lt_of_le_of_lt (Nat.le_of_lt_succ i.isLt) hnm)

/-- If the origin is bad, the same endpoint set is exactly the singleton
origin, since every positive-length witness would require a good origin. -/
theorem oriented_endpoint_set_eq_singleton_of_origin_bad
    (G : Set (ℕ × ℕ)) (hbad : (0, 0) ∉ G) :
    {x : ℕ × ℕ | ∃ n : ℕ, ∃ q : Fin (n + 1) → ℕ × ℕ,
      q 0 = (0, 0) ∧ q (Fin.last n) = x ∧
      (∀ i : Fin n,
        q i.succ = q i.castSucc + (1, 0) ∨ q i.succ = q i.castSucc + (0, 1)) ∧
      ∀ i : Fin (n + 1), (i : ℕ) < n → q i ∈ G} = {(0, 0)} := by
  ext x
  constructor
  · rintro ⟨n, q, hzero, hlast, _, hgood⟩
    have hn : n = 0 := by
      by_contra hn
      apply hbad
      rw [← hzero]
      exact hgood 0 (show (0 : ℕ) < n by omega)
    subst n
    have heq : (Fin.last 0 : Fin 1) = 0 := rfl
    rw [heq, hzero] at hlast
    exact Set.mem_singleton_iff.mpr hlast.symm
  · intro hx
    have hxzero : x = (0, 0) := Set.mem_singleton_iff.mp hx
    refine ⟨0, fun _ => (0, 0), rfl, hxzero.symm, ?_, ?_⟩
    · intro i
      exact Fin.elim0 i
    · intro i hi
      omega

end LPPDifferentiability
