/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Paths.FloorSegment
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Interiority of a floor partition

This file gives the cone and cutoff facts for the floor partition used in the proof of
Lemma 3.1 of the differentiability preprint.

## References

- C. Janjigian, F. Rassoul-Agha and T. Seppäläinen, *Differentiability of the shape function in
  the planar corner growth model*, preprint.
-/

public section

namespace LPPDifferentiability

/-- Dividing by a positive number preserves the adapted cone. -/
theorem adapted_cone_div (a theta x y b : ℝ) (hb : 0 < b)
    (h : |(1-a)*x-a*y| ≤ (min a (1-a)-theta)*(x+y)) :
    |(1-a)*(x/b)-a*(y/b)| ≤ (min a (1-a)-theta)*(x/b+y/b) := by
  have heq : (1-a)*(x/b)-a*(y/b) = ((1-a)*x-a*y)/b := by ring
  rw [heq, abs_div, abs_of_pos hb]
  have hr : (min a (1-a)-theta)*(x/b+y/b) =
      ((min a (1-a)-theta)*(x+y))/b := by ring
  rw [hr]
  exact div_le_div_of_nonneg_right h hb.le

/-- The explicit cutoff forces strictly positive piece length. -/
theorem floorSegment_cutoff_positive (a theta t : ℝ)
    (htheta : 0 < theta) (hinterior : theta < min a (1-a))
    (hcut : theta/2*t ≥ 2+2*(min a (1-a)-theta/2)) : 2 < t := by
  have hc : 0 < min a (1-a)-theta/2 := by linarith
  have hmin : min a (1-a) ≤ 1/2 := by
    have h1 := min_le_left a (1-a)
    have h2 := min_le_right a (1-a)
    linarith
  have ht : theta < 1/2 := hinterior.trans_le hmin
  by_contra h
  have ht2 : t ≤ 2 := le_of_not_gt h
  have hm := mul_le_mul_of_nonneg_left ht2 (show 0 ≤ theta/2 by linarith)
  nlinarith

/-- Both rounding estimates come from the floor-increment bound.
The cutoff is exactly the one used in the proof of Lemma 3.1 of the differentiability
preprint. -/
theorem floorSegment_increment_interior (a theta : ℝ)
    (ha0 : 0 < a) (ha1 : a < 1) (htheta : 0 < theta)
    (hinterior : theta < min a (1-a))
    (d : ℕ × ℕ) (B j : ℕ) (hB : 1 ≤ B)
    (hd : |(1-a)*(d.1:ℝ)-a*(d.2:ℝ)| ≤
      (min a (1-a)-theta)*((d.1:ℝ)+(d.2:ℝ)))
    (hcut : theta/2*(((d.1:ℝ)+(d.2:ℝ))/(B:ℝ)) ≥
      2+2*(min a (1-a)-theta/2)) :
    let k : ℕ → ℕ × ℕ := fun n => (n*d.1/B,n*d.2/B)
    let Δ : ℕ → ℕ × ℕ := fun n =>
      ((k (n+1)).1-(k n).1,(k (n+1)).2-(k n).2)
    0 < ((Δ j).1:ℝ)+((Δ j).2:ℝ) ∧
    |(1-a)*((Δ j).1:ℝ)-a*((Δ j).2:ℝ)| ≤
      (min a (1-a)-theta/2)*(((Δ j).1:ℝ)+((Δ j).2:ℝ)) := by
  intro k Δ
  have hb : 0 < (B:ℝ) := by exact_mod_cast (show 0 < B by omega)
  have hround := floorSegment_increment_bounds d B j hB
  change |((Δ j).1:ℝ)-(d.1:ℝ)/(B:ℝ)|+
      |((Δ j).2:ℝ)-(d.2:ℝ)/(B:ℝ)| ≤ 2 ∧
    ((d.1+d.2:ℕ):ℝ)/(B:ℝ)-2 ≤ ((Δ j).1:ℝ)+((Δ j).2:ℝ) ∧
    ((Δ j).1:ℝ)+((Δ j).2:ℝ) ≤ ((d.1+d.2:ℕ):ℝ)/(B:ℝ)+2 at hround
  simp only [Nat.cast_add] at hround
  have hscaled := adapted_cone_div a theta (d.1:ℝ) (d.2:ℝ) (B:ℝ) hb hd
  have hrhoError :
      |(1-a)*(((Δ j).1:ℝ)-(d.1:ℝ)/(B:ℝ))-
        a*(((Δ j).2:ℝ)-(d.2:ℝ)/(B:ℝ))| ≤ 2 := by
    calc
      _ ≤ |(1-a)*(((Δ j).1:ℝ)-(d.1:ℝ)/(B:ℝ))|+
          |a*(((Δ j).2:ℝ)-(d.2:ℝ)/(B:ℝ))| := abs_sub _ _
      _ = (1-a)*|((Δ j).1:ℝ)-(d.1:ℝ)/(B:ℝ)|+
          a*|((Δ j).2:ℝ)-(d.2:ℝ)/(B:ℝ)| := by
        rw [abs_mul, abs_mul, abs_of_pos (sub_pos.mpr ha1), abs_of_pos ha0]
      _ ≤ |((Δ j).1:ℝ)-(d.1:ℝ)/(B:ℝ)|+
          |((Δ j).2:ℝ)-(d.2:ℝ)/(B:ℝ)| := by
        nlinarith [abs_nonneg (((Δ j).1:ℝ)-(d.1:ℝ)/(B:ℝ)),
          abs_nonneg (((Δ j).2:ℝ)-(d.2:ℝ)/(B:ℝ))]
      _ ≤ 2 := hround.1
  have hrho : |(1-a)*((Δ j).1:ℝ)-a*((Δ j).2:ℝ)| ≤
      (min a (1-a)-theta)*(((d.1:ℝ)+(d.2:ℝ))/(B:ℝ))+2 := by
    have htriangle := abs_add_le
      ((1-a)*((d.1:ℝ)/(B:ℝ))-a*((d.2:ℝ)/(B:ℝ)))
      ((1-a)*(((Δ j).1:ℝ)-(d.1:ℝ)/(B:ℝ))-
        a*(((Δ j).2:ℝ)-(d.2:ℝ)/(B:ℝ)))
    have heq : (1-a)*((d.1:ℝ)/(B:ℝ))-a*((d.2:ℝ)/(B:ℝ))+
      ((1-a)*(((Δ j).1:ℝ)-(d.1:ℝ)/(B:ℝ))-
        a*(((Δ j).2:ℝ)-(d.2:ℝ)/(B:ℝ))) =
      (1-a)*((Δ j).1:ℝ)-a*((Δ j).2:ℝ) := by ring
    rw [heq] at htriangle
    rw [← add_div] at hscaled
    linarith
  have hpositive := floorSegment_cutoff_positive a theta
    (((d.1:ℝ)+(d.2:ℝ))/(B:ℝ)) htheta hinterior hcut
  have hc : 0 ≤ min a (1-a)-theta/2 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hround.2.1 hc
  constructor
  · linarith [hround.2.1]
  · nlinarith

end LPPDifferentiability
