/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.Path
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-! # Merging two admissible paths on the same levels

For a real parameter `a`, the transverse coordinate of a site `z` is
`(1 - a) * z.1 - a * z.2`. Two sites on the same level differ by `(t, -t)` for
an integer `t`, so their transverse coordinates differ by exactly `t`. An
admissible step changes the first coordinate by `0` or `1`, so along two paths
on the same levels the difference of first coordinates is an integer sequence
with steps in `{-1, 0, 1}`. If it changes sign, it must vanish in between,
which means the two paths share a vertex.
-/

public section

namespace LPPDifferentiability

/-- Two sites on the same level have transverse coordinates differing by the
first-coordinate difference. -/
private theorem rcoord_sub_same_level (a : ℝ) (p1 p2 q1 q2 : ℤ)
    (h : p1 + p2 = q1 + q2) :
    (1 - a) * (p1 : ℝ) - a * (p2 : ℝ) - ((1 - a) * (q1 : ℝ) - a * (q2 : ℝ)) =
      ((p1 - q1 : ℤ) : ℝ) := by
  have hr : (p1 : ℝ) + (p2 : ℝ) = (q1 : ℝ) + (q2 : ℝ) := by exact_mod_cast h
  push_cast
  linear_combination (-a) * hr

/-- Along an admissible path the level of the vertex with local time `j` is
`u.1 + u.2 + j`. -/
private theorem path_level {u : Lattice} {d : ℕ × ℕ} (p : Path u d) :
    ∀ j : ℕ, ∀ hj : j < d.1 + d.2 + 1,
      (p.vertex ⟨j, hj⟩).1 + (p.vertex ⟨j, hj⟩).2 = u.1 + u.2 + (j : ℤ) := by
  intro j
  induction j with
  | zero =>
    intro hj
    have hx0 : p.vertex ⟨0, hj⟩ = u := by simpa using p.start
    rw [hx0]
    simp
  | succ j ih =>
    intro hj
    have hlt : j < d.1 + d.2 + 1 := by omega
    have hlt' : j < d.1 + d.2 := by omega
    have ih' := ih hlt
    have hs := p.step ⟨j, hlt'⟩
    have e1 : Fin.succ (⟨j, hlt'⟩ : Fin (d.1 + d.2)) = ⟨j + 1, hj⟩ := rfl
    have e2 : Fin.castSucc (⟨j, hlt'⟩ : Fin (d.1 + d.2)) = ⟨j, hlt⟩ := rfl
    rw [e1, e2] at hs
    rcases hs with hs | hs <;> rw [hs] <;> simp only [Prod.fst_add, Prod.snd_add] <;>
      omega

/-- Along an admissible path the first coordinate increases by `0` or `1` at
each step. -/
private theorem path_fst_step {u : Lattice} {d : ℕ × ℕ} (p : Path u d) (j : ℕ)
    (hj : j < d.1 + d.2 + 1) (hj1 : j + 1 < d.1 + d.2 + 1) :
    (p.vertex ⟨j + 1, hj1⟩).1 - (p.vertex ⟨j, hj⟩).1 = 0 ∨
      (p.vertex ⟨j + 1, hj1⟩).1 - (p.vertex ⟨j, hj⟩).1 = 1 := by
  have hlt : j < d.1 + d.2 := by omega
  have hs := p.step ⟨j, hlt⟩
  have e1 : Fin.succ (⟨j, hlt⟩ : Fin (d.1 + d.2)) = ⟨j + 1, hj1⟩ := rfl
  have e2 : Fin.castSucc (⟨j, hlt⟩ : Fin (d.1 + d.2)) = ⟨j, hj⟩ := rfl
  rw [e1, e2] at hs
  rcases hs with hs | hs <;> rw [hs] <;> simp only [Prod.fst_add] <;>
    omega

/-- A sequence of integers starting positive and ending negative, with steps in
`{-1, 0, 1}`, vanishes at some index strictly between its endpoints. -/
private theorem exists_zero_between (F : ℕ → ℤ) (N : ℕ) (h0 : 0 < F 0)
    (hN : F N < 0)
    (hstep : ∀ j, j < N → -1 ≤ F (j + 1) - F j ∧ F (j + 1) - F j ≤ 1) :
    ∃ j, 0 < j ∧ j < N ∧ F j = 0 := by
  by_contra hcon
  have hcon' : ∀ j, 0 < j → j < N → F j ≠ 0 := fun j h1 h2 h3 => hcon ⟨j, h1, h2, h3⟩
  have hpos : ∀ j, j < N → 0 < F j := by
    intro j
    induction j with
    | zero => intro _; exact h0
    | succ j ih =>
      intro hj
      have hprev := ih (by omega)
      have hne := hcon' (j + 1) (by omega) hj
      have hd := hstep j (by omega)
      omega
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0
    omega
  · have h1 := hpos (N - 1) (by omega)
    have h2 := hstep (N - 1) (by omega)
    have e : N - 1 + 1 = N := by omega
    rw [e] at h2
    omega

/-- Two admissible paths `x` from `u` and `y` from `u'`, with the same starting
level and the same length, whose transverse coordinates satisfy
`rcoord(u') < rcoord(u)` at the start and `rcoord(u + d) < rcoord(u' + d')` at
the end, share a vertex strictly between their endpoints. The transverse
coordinate is `(1 - a) * z.1 - a * z.2`. -/
theorem admissible_paths_merge (a : ℝ) :
    ∀ (u u' : Lattice) (d d' : ℕ × ℕ) (x : Path u d) (y : Path u' d'),
      u.1 + u.2 = u'.1 + u'.2 → ∀ hd : d.1 + d.2 = d'.1 + d'.2,
      (1 - a) * (u'.1 : ℝ) - a * (u'.2 : ℝ) < (1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ) →
      (1 - a) * ((u.1 + d.1 : ℤ) : ℝ) - a * ((u.2 + d.2 : ℤ) : ℝ) <
        (1 - a) * ((u'.1 + d'.1 : ℤ) : ℝ) - a * ((u'.2 + d'.2 : ℤ) : ℝ) →
      ∃ i : ℕ, ∃ hi : i < d.1 + d.2, 0 < i ∧
        x.vertex ⟨i, by omega⟩ = y.vertex ⟨i, by omega⟩ := by
  intro u u' d d' x y hlev hd h0 hN
  have hyl : ∀ j, j < d.1 + d.2 + 1 → j < d'.1 + d'.2 + 1 := fun j hj => by omega
  obtain ⟨F, hF⟩ : ∃ F : ℕ → ℤ, ∀ j (hj : j < d.1 + d.2 + 1),
      F j = (x.vertex ⟨j, hj⟩).1 - (y.vertex ⟨j, hyl j hj⟩).1 :=
    ⟨fun j => if h : j < d.1 + d.2 + 1 then
        (x.vertex ⟨j, h⟩).1 - (y.vertex ⟨j, hyl j h⟩).1 else 0,
      fun j hj => by simp [hj]⟩
  -- Step bounds for the difference of first coordinates.
  have hstep : ∀ j, j < d.1 + d.2 → -1 ≤ F (j + 1) - F j ∧ F (j + 1) - F j ≤ 1 := by
    intro j hj
    have hj0 : j < d.1 + d.2 + 1 := by omega
    have hj1 : j + 1 < d.1 + d.2 + 1 := by omega
    rw [hF (j + 1) hj1, hF j hj0]
    have ex := path_fst_step x j hj0 hj1
    have ey := path_fst_step y j (hyl j hj0) (hyl (j + 1) hj1)
    omega
  -- Sign at the start.
  have hz : 0 < d.1 + d.2 + 1 := by omega
  have hx0 : x.vertex ⟨0, hz⟩ = u := by simpa using x.start
  have hy0 : y.vertex ⟨0, hyl 0 hz⟩ = u' := by simpa using y.start
  have hc0 := rcoord_sub_same_level a u.1 u.2 u'.1 u'.2 hlev
  have hpos0 : (0 : ℝ) < ((u.1 - u'.1 : ℤ) : ℝ) := by linarith
  have hpos0' : 0 < u.1 - u'.1 := by exact_mod_cast hpos0
  have hF0 : 0 < F 0 := by
    rw [hF 0 hz, hx0, hy0]
    omega
  -- Sign at the end.
  have hN0 : d.1 + d.2 < d.1 + d.2 + 1 := by omega
  have hxN : x.vertex ⟨d.1 + d.2, hN0⟩ = u + ((d.1 : ℤ), (d.2 : ℤ)) := x.finish
  have hyN : y.vertex ⟨d.1 + d.2, hyl (d.1 + d.2) hN0⟩ = u' + ((d'.1 : ℤ), (d'.2 : ℤ)) := by
    have e : (⟨d.1 + d.2, hyl (d.1 + d.2) hN0⟩ : Fin (d'.1 + d'.2 + 1)) =
        Fin.last (d'.1 + d'.2) := Fin.ext hd
    rw [e]
    exact y.finish
  have hlevN : (u.1 + (d.1 : ℤ)) + (u.2 + (d.2 : ℤ)) =
      (u'.1 + (d'.1 : ℤ)) + (u'.2 + (d'.2 : ℤ)) := by
    omega
  have hcN := rcoord_sub_same_level a (u.1 + (d.1 : ℤ)) (u.2 + (d.2 : ℤ))
    (u'.1 + (d'.1 : ℤ)) (u'.2 + (d'.2 : ℤ)) hlevN
  have hNr : ((u.1 + (d.1 : ℤ) - (u'.1 + (d'.1 : ℤ)) : ℤ) : ℝ) < 0 := by
    linarith
  have hNint : u.1 + (d.1 : ℤ) - (u'.1 + (d'.1 : ℤ)) < 0 := by
    exact_mod_cast hNr
  have hFN : F (d.1 + d.2) < 0 := by
    rw [hF (d.1 + d.2) hN0, hxN, hyN]
    simp only [Prod.fst_add]
    omega
  -- Discrete intermediate value step: a common vertex strictly inside.
  obtain ⟨j, hjpos, hjN, hFj⟩ := exists_zero_between F (d.1 + d.2) hF0 hFN hstep
  have hj0 : j < d.1 + d.2 + 1 := by omega
  have hFj' := hF j hj0
  have hlx := path_level x j hj0
  have hly := path_level y j (hyl j hj0)
  have hcoord1 : (x.vertex ⟨j, hj0⟩).1 = (y.vertex ⟨j, hyl j hj0⟩).1 := by
    omega
  have hcoord2 : (x.vertex ⟨j, hj0⟩).2 = (y.vertex ⟨j, hyl j hj0⟩).2 := by
    omega
  exact ⟨j, hjN, hjpos, Prod.ext hcoord1 hcoord2⟩

end LPPDifferentiability
