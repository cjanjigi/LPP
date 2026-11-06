/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.Lattice

import Mathlib.Data.Int.DivMod
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Coarse sampling of a bounded lattice walk

The finite-window sampling step used to place a lattice walk inside a chain of
larger-scale boxes. This file proves only that geometric sublemma; it does not
define animals or prove their counting estimate.
-/

public section

namespace LPPDifferentiability

private theorem int_ediv_difference_le_one {L x y : ℤ} (hL : 0 < L)
    (hxy : x - y ≤ L) : x / L - y / L ≤ 1 := by
  by_contra hnot
  have hquot : 2 ≤ x / L - y / L := by omega
  have hmul : L * 2 ≤ L * (x / L - y / L) :=
    mul_le_mul_of_nonneg_left hquot hL.le
  have hx_nonneg : 0 ≤ x % L := Int.emod_nonneg x hL.ne'
  have hy_lt : y % L < L := Int.emod_lt_of_pos y hL
  have hrem : -L < x % L - y % L := by omega
  have hx_div : L * (x / L) + x % L = x := Int.mul_ediv_add_emod x L
  have hy_div : L * (y / L) + y % L = y := Int.mul_ediv_add_emod y L
  have hdecomp : x - y = L * (x / L - y / L) + (x % L - y % L) := by
    calc
      x - y = (L * (x / L) + x % L) - (L * (y / L) + y % L) := by
        rw [hx_div, hy_div]
      _ = L * (x / L - y / L) + (x % L - y % L) := by ring
  have hlarge : L < x - y := by linarith
  exact (not_lt_of_ge hxy) hlarge

/-- Euclidean floor quotients at a positive integer scale differ by at most
one when the original integers differ by at most that scale. This includes
negative integers because integer `%` uses a nonnegative remainder. -/
theorem int_ediv_sub_ediv_abs_le_one {L x y : ℤ} (hL : 0 < L)
    (hxy : |x - y| ≤ L) : |x / L - y / L| ≤ 1 := by
  apply abs_le.mpr
  constructor
  · have hyx : y - x ≤ L := by
      have h := (abs_le.mp hxy).1
      omega
    have h := int_ediv_difference_le_one hL hyx
    linarith
  · exact int_ediv_difference_le_one hL (abs_le.mp hxy).2

/-- Rounding an integer down by Euclidean division moves it by less than the
positive scale. -/
theorem int_ediv_rounding_error_abs_lt {L x : ℤ} (hL : 0 < L) :
    |x - L * (x / L)| < L := by
  have hdiv : L * (x / L) + x % L = x := Int.mul_ediv_add_emod x L
  have hrem_nonneg : 0 ≤ x % L := Int.emod_nonneg x hL.ne'
  have hrem_lt : x % L < L := Int.emod_lt_of_pos x hL
  have herror : x - L * (x / L) = x % L := by linarith
  rw [herror, abs_of_nonneg hrem_nonneg]
  exact hrem_lt

/-- A walk whose one-step coordinate changes are at most one has coordinate
displacement at most the elapsed number of steps on the stated finite window. -/
theorem bounded_integer_walk_abs_sub_le (w : ℕ → ℤ) (n : ℕ)
    (hstep : ∀ t, t < 2 * n → |w (t + 1) - w t| ≤ 1)
    {s t : ℕ} (hst : s ≤ t) (ht : t ≤ 2 * n) :
    |w t - w s| ≤ (t - s : ℤ) := by
  induction t using Nat.strong_induction_on generalizing s with
  | h t ih =>
    by_cases hst_eq : s = t
    · subst s
      simp
    · have hst_lt : s < t := lt_of_le_of_ne hst hst_eq
      have hprev_s : s ≤ t - 1 := by omega
      have hprev_t : t - 1 ≤ 2 * n := by omega
      have hprev := ih (t - 1) (by omega) hprev_s hprev_t
      have hprev' : |w (t - 1) - w s| ≤ ((t - 1 - s : ℕ) : ℤ) := by
        simpa only [Nat.cast_sub hprev_s] using hprev
      have ht_pos : 1 ≤ t := by omega
      have hstep' : |w t - w (t - 1)| ≤ 1 := by
        simpa only [Nat.sub_add_cancel ht_pos] using hstep (t - 1) (by omega)
      have htriangle :
          |w t - w s| ≤ |w t - w (t - 1)| + |w (t - 1) - w s| := by
        calc
          |w t - w s| = |(w t - w (t - 1)) + (w (t - 1) - w s)| := by
            congr 1
            ring
          _ ≤ |w t - w (t - 1)| + |w (t - 1) - w s| := abs_add_le _ _
      calc
        |w t - w s| ≤ |w t - w (t - 1)| + |w (t - 1) - w s| := htriangle
        _ ≤ 1 + ((t - 1 - s : ℕ) : ℤ) := add_le_add hstep' hprev'
        _ = (t - s : ℤ) := by
          exact_mod_cast (show 1 + (t - 1 - s : ℕ) = t - s by omega)

/-- A bounded integer walk admits a coarse sampled walk. Every value in the
finite time window lies in one of the closed coordinatewise boxes of radius
`2*l` centered at `l` times a sampled value. The range `l ≤ n` is kept,
although this construction only needs the positive-scale condition. -/
theorem exists_coarse_walk_cover (l n : ℕ) (hl : 1 ≤ l) (_hln : l ≤ n)
    (w : ℕ → Lattice) (hw0 : w 0 = 0)
    (hstep : ∀ t, t < 2 * n →
      |(w (t + 1)).1 - (w t).1| ≤ 1 ∧
      |(w (t + 1)).2 - (w t).2| ≤ 1) :
    ∃ u : Fin ((2 * n / l) + 1) → Lattice,
      u 0 = 0 ∧
      (∀ i : Fin (2 * n / l),
        |(u i.succ).1 - (u i.castSucc).1| ≤ 1 ∧
        |(u i.succ).2 - (u i.castSucc).2| ≤ 1) ∧
      (∀ t, t ≤ 2 * n → ∃ i : Fin ((2 * n / l) + 1),
        |(w t).1 - (l : ℤ) * (u i).1| ≤ 2 * (l : ℤ) ∧
        |(w t).2 - (l : ℤ) * (u i).2| ≤ 2 * (l : ℤ)) := by
  let r : ℕ := 2 * n / l
  let u : Fin (r + 1) → Lattice := fun i =>
    ((w (i.val * l)).1 / (l : ℤ), (w (i.val * l)).2 / (l : ℤ))
  have hl_nat : 0 < l := by omega
  have hl_int : (0 : ℤ) < (l : ℤ) := by exact_mod_cast hl_nat
  have hr_mul : r * l ≤ 2 * n := by
    dsimp [r]
    exact Nat.div_mul_le_self (2 * n) l
  refine ⟨u, ?_⟩
  constructor
  · simp [u, hw0]
  constructor
  · intro i
    have hi_lt := i.isLt
    have hi_succ : i.val + 1 ≤ r := by omega
    have hi_right : (i.val + 1) * l ≤ 2 * n := by
      calc
        (i.val + 1) * l ≤ r * l := Nat.mul_le_mul_right l hi_succ
        _ ≤ 2 * n := hr_mul
    have htimes : (i.val + 1) * l = i.val * l + l := by
      rw [Nat.add_mul, Nat.one_mul]
    have hfirst_walk :
        |(w ((i.val + 1) * l)).1 - (w (i.val * l)).1| ≤ (l : ℤ) := by
      have h := bounded_integer_walk_abs_sub_le (fun t => (w t).1) n
        (fun t ht => (hstep t ht).1) (s := i.val * l) (t := i.val * l + l)
        (by omega) (by simpa [htimes] using hi_right)
      simpa only [htimes, Nat.cast_add, add_sub_cancel_left] using h
    have hsecond_walk :
        |(w ((i.val + 1) * l)).2 - (w (i.val * l)).2| ≤ (l : ℤ) := by
      have h := bounded_integer_walk_abs_sub_le (fun t => (w t).2) n
        (fun t ht => (hstep t ht).2) (s := i.val * l) (t := i.val * l + l)
        (by omega) (by simpa [htimes] using hi_right)
      simpa only [htimes, Nat.cast_add, add_sub_cancel_left] using h
    constructor
    · have h := int_ediv_sub_ediv_abs_le_one hl_int hfirst_walk
      simpa only [u, Fin.val_succ, Fin.val_castSucc] using h
    · have h := int_ediv_sub_ediv_abs_le_one hl_int hsecond_walk
      simpa only [u, Fin.val_succ, Fin.val_castSucc] using h
  · intro t ht
    let j : ℕ := t / l
    have hj : j ≤ r := by
      dsimp [j, r]
      exact Nat.div_le_div_right ht
    let s : ℕ := j * l
    have hs_le : s ≤ t := by
      dsimp [s, j]
      exact Nat.div_mul_le_self t l
    have hdecomp : s + t % l = t := by
      dsimp [s, j]
      simpa [Nat.mul_comm] using Nat.div_add_mod t l
    have hgap : t - s < l := by
      rw [show t - s = t % l by omega]
      exact Nat.mod_lt t hl_nat
    have hfirst_displacement : |(w t).1 - (w s).1| ≤ (l : ℤ) := by
      calc
        |(w t).1 - (w s).1| ≤ (t - s : ℤ) :=
          bounded_integer_walk_abs_sub_le (fun a => (w a).1) n
            (fun a ha => (hstep a ha).1) hs_le ht
        _ ≤ (l : ℤ) := by exact_mod_cast (show t - s ≤ l by omega)
    have hsecond_displacement : |(w t).2 - (w s).2| ≤ (l : ℤ) := by
      calc
        |(w t).2 - (w s).2| ≤ (t - s : ℤ) :=
          bounded_integer_walk_abs_sub_le (fun a => (w a).2) n
            (fun a ha => (hstep a ha).2) hs_le ht
        _ ≤ (l : ℤ) := by exact_mod_cast (show t - s ≤ l by omega)
    have hfirst_rounding :
        |(w s).1 - (l : ℤ) * ((w s).1 / (l : ℤ))| ≤ (l : ℤ) :=
      (int_ediv_rounding_error_abs_lt (L := (l : ℤ)) (x := (w s).1) hl_int).le
    have hsecond_rounding :
        |(w s).2 - (l : ℤ) * ((w s).2 / (l : ℤ))| ≤ (l : ℤ) :=
      (int_ediv_rounding_error_abs_lt (L := (l : ℤ)) (x := (w s).2) hl_int).le
    have hfirst_cover : |(w t).1 - (l : ℤ) * ((w s).1 / (l : ℤ))| ≤
        2 * (l : ℤ) := by
      calc
        |(w t).1 - (l : ℤ) * ((w s).1 / (l : ℤ))| =
            |((w t).1 - (w s).1) + ((w s).1 - (l : ℤ) * ((w s).1 / (l : ℤ)))| := by
          congr 1
          ring
        _ ≤ |(w t).1 - (w s).1| +
            |(w s).1 - (l : ℤ) * ((w s).1 / (l : ℤ))| := abs_add_le _ _
        _ ≤ (l : ℤ) + (l : ℤ) := add_le_add hfirst_displacement hfirst_rounding
        _ = 2 * (l : ℤ) := by ring
    have hsecond_cover : |(w t).2 - (l : ℤ) * ((w s).2 / (l : ℤ))| ≤
        2 * (l : ℤ) := by
      calc
        |(w t).2 - (l : ℤ) * ((w s).2 / (l : ℤ))| =
            |((w t).2 - (w s).2) + ((w s).2 - (l : ℤ) * ((w s).2 / (l : ℤ)))| := by
          congr 1
          ring
        _ ≤ |(w t).2 - (w s).2| +
            |(w s).2 - (l : ℤ) * ((w s).2 / (l : ℤ))| := abs_add_le _ _
        _ ≤ (l : ℤ) + (l : ℤ) := add_le_add hsecond_displacement hsecond_rounding
        _ = 2 * (l : ℤ) := by ring
    refine ⟨⟨j, Nat.lt_succ_of_le (by simpa [r] using hj)⟩, ?_⟩
    constructor
    · simpa only [u, Fin.val_mk, s] using hfirst_cover
    · simpa only [u, Fin.val_mk, s] using hsecond_cover

end LPPDifferentiability
