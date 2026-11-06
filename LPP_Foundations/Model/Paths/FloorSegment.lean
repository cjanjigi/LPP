/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Paths.Geometry

import Mathlib.Data.Int.DivMod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! Floor-partition estimates for a path rectangle near a segment. -/

@[expose] public section

namespace LPPDifferentiability

private theorem nat_div_floor_error (n B : ℕ) (hB : 0 < B) :
    -1 < ((n / B : ℕ) : ℝ) - (n : ℝ) / (B : ℝ) ∧
      ((n / B : ℕ) : ℝ) - (n : ℝ) / (B : ℝ) ≤ 0 := by
  have hBReal : 0 < (B : ℝ) := by exact_mod_cast hB
  have hdivMul : n / B * B ≤ n := Nat.div_mul_le_self n B
  have hdivMulReal : ((n / B : ℕ) : ℝ) * (B : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hdivMul
  have hrem : n % B < B := Nat.mod_lt n hB
  have hdecomp : n / B * B + n % B = n := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod n B
  have hltNat : n < (n / B + 1) * B := by
    calc
      n = n / B * B + n % B := hdecomp.symm
      _ < n / B * B + B := Nat.add_lt_add_left hrem _
      _ = (n / B + 1) * B := by rw [Nat.add_mul, Nat.one_mul]
  have hdivLo : ((n / B : ℕ) : ℝ) ≤ (n : ℝ) / (B : ℝ) :=
    (le_div_iff₀ hBReal).2 hdivMulReal
  have hdivHi : (n : ℝ) / (B : ℝ) < ((n / B + 1 : ℕ) : ℝ) :=
    (div_lt_iff₀ hBReal).2 (by exact_mod_cast hltNat)
  simp only [Nat.cast_add, Nat.cast_one] at hdivHi
  constructor <;> linarith

private theorem nat_div_sub_increment_error (a b B : ℕ) (hB : 0 < B) :
    |(((a + b) / B - a / B : ℕ) : ℝ) - (b : ℝ) / (B : ℝ)| ≤ 1 := by
  have hquot : a / B ≤ (a + b) / B :=
    Nat.div_le_div_right (Nat.le_add_right a b)
  have hnow := nat_div_floor_error a B hB
  have hnext := nat_div_floor_error (a + b) B hB
  have hscale : ((a + b : ℕ) : ℝ) / (B : ℝ) =
      (a : ℝ) / (B : ℝ) + (b : ℝ) / (B : ℝ) := by
    push_cast
    ring
  rw [Nat.cast_sub hquot]
  have hrewrite :
      (((a + b) / B : ℕ) : ℝ) - ((a / B : ℕ) : ℝ) - (b : ℝ) / (B : ℝ) =
        ((((a + b) / B : ℕ) : ℝ) - (a + b : ℕ) / (B : ℝ)) -
          (((a / B : ℕ) : ℝ) - (a : ℝ) / (B : ℝ)) := by
    rw [hscale]
    ring
  rw [show
      |(((a + b) / B : ℕ) : ℝ) - ((a / B : ℕ) : ℝ) - (b : ℝ) / (B : ℝ)| =
        |((((a + b) / B : ℕ) : ℝ) - (a + b : ℕ) / (B : ℝ)) -
          (((a / B : ℕ) : ℝ) - (a : ℝ) / (B : ℝ))| by
      rw [hrewrite]]
  apply abs_le.mpr
  constructor <;> linarith [hnext.1, hnext.2, hnow.1, hnow.2]

/-- The literal coordinatewise floor partition has the stated endpoints. -/
theorem floorSegment_endpoints (u : Lattice) (d : ℕ × ℕ) (B : ℕ)
    (hB : 1 ≤ B) :
    let k : ℕ → ℕ × ℕ := fun j => (j * d.1 / B, j * d.2 / B)
    let u' : ℕ → Lattice := fun j =>
      u + (((k j).1 : ℤ), ((k j).2 : ℤ))
    u' 0 = u ∧ u' B = u + ((d.1 : ℤ), (d.2 : ℤ)) := by
  dsimp only
  constructor
  · apply Prod.ext <;> simp
  · have hBPos : 0 < B := by omega
    apply Prod.ext
    · simp only [Prod.fst_add, Nat.mul_div_cancel_left _ hBPos]
    · simp only [Prod.snd_add, Nat.mul_div_cancel_left _ hBPos]

/-- Consecutive points in the floor partition are coordinatewise ordered. -/
theorem floorSegment_monotone (u : Lattice) (d : ℕ × ℕ) (B j : ℕ)
    (_hB : 1 ≤ B) :
    let k : ℕ → ℕ × ℕ := fun n => (n * d.1 / B, n * d.2 / B)
    let u' : ℕ → Lattice := fun n =>
      u + (((k n).1 : ℤ), ((k n).2 : ℤ))
    u' j ≤ u' (j + 1) := by
  dsimp only
  constructor
  · have hmul : j * d.1 ≤ (j + 1) * d.1 :=
      Nat.mul_le_mul_right d.1 (Nat.le_succ j)
    have hdiv : j * d.1 / B ≤ (j + 1) * d.1 / B :=
      Nat.div_le_div_right hmul
    have hdivInt : ((j * d.1 / B : ℕ) : ℤ) ≤ (((j + 1) * d.1 / B : ℕ) : ℤ) := by
      exact_mod_cast hdiv
    simpa only [Prod.fst_add] using add_le_add_right hdivInt u.1
  · have hmul : j * d.2 ≤ (j + 1) * d.2 :=
      Nat.mul_le_mul_right d.2 (Nat.le_succ j)
    have hdiv : j * d.2 / B ≤ (j + 1) * d.2 / B :=
      Nat.div_le_div_right hmul
    have hdivInt : ((j * d.2 / B : ℕ) : ℤ) ≤ (((j + 1) * d.2 / B : ℕ) : ℤ) := by
      exact_mod_cast hdiv
    simpa only [Prod.snd_add] using add_le_add_right hdivInt u.2

/-- Natural subtraction of consecutive floor points is the actual displacement. -/
theorem floorSegment_increment (u : Lattice) (d : ℕ × ℕ) (B j : ℕ)
    (_hB : 1 ≤ B) :
    let k : ℕ → ℕ × ℕ := fun n => (n * d.1 / B, n * d.2 / B)
    let u' : ℕ → Lattice := fun n =>
      u + (((k n).1 : ℤ), ((k n).2 : ℤ))
    let Δ : ℕ → ℕ × ℕ := fun n =>
      ((k (n + 1)).1 - (k n).1, (k (n + 1)).2 - (k n).2)
    u' j + (((Δ j).1 : ℤ), ((Δ j).2 : ℤ)) = u' (j + 1) := by
  dsimp only
  apply Prod.ext
  · simp only [Prod.fst_add]
    have hmul : j * d.1 ≤ (j + 1) * d.1 :=
      Nat.mul_le_mul_right d.1 (Nat.le_succ j)
    have hdiv : j * d.1 / B ≤ (j + 1) * d.1 / B :=
      Nat.div_le_div_right hmul
    rw [Nat.cast_sub hdiv]
    ring
  · simp only [Prod.snd_add]
    have hmul : j * d.2 ≤ (j + 1) * d.2 :=
      Nat.mul_le_mul_right d.2 (Nat.le_succ j)
    have hdiv : j * d.2 / B ≤ (j + 1) * d.2 / B :=
      Nat.div_le_div_right hmul
    rw [Nat.cast_sub hdiv]
    ring

/-- Each floor-partition point is within real L1 distance two of its segment point. -/
theorem floorSegment_anchor_error (u : Lattice) (d : ℕ × ℕ) (B j : ℕ)
    (hB : 1 ≤ B) :
    let k : ℕ → ℕ × ℕ := fun n => (n * d.1 / B, n * d.2 / B)
    let u' : ℕ → Lattice := fun n =>
      u + (((k n).1 : ℤ), ((k n).2 : ℤ))
    |((u' j).1 : ℝ) - ((u.1 : ℝ) + (j : ℝ) / (B : ℝ) * (d.1 : ℝ))| +
        |((u' j).2 : ℝ) - ((u.2 : ℝ) + (j : ℝ) / (B : ℝ) * (d.2 : ℝ))| ≤ 2 := by
  dsimp only
  have hBPos : 0 < B := by omega
  have hfirst := nat_div_floor_error (j * d.1) B hBPos
  have hsecond := nat_div_floor_error (j * d.2) B hBPos
  have hfirstScale : ((j * d.1 : ℕ) : ℝ) / (B : ℝ) =
      (j : ℝ) / (B : ℝ) * (d.1 : ℝ) := by
    push_cast
    ring
  have hsecondScale : ((j * d.2 : ℕ) : ℝ) / (B : ℝ) =
      (j : ℝ) / (B : ℝ) * (d.2 : ℝ) := by
    push_cast
    ring
  have hfirstBound :
      |((j * d.1 / B : ℕ) : ℝ) - (j : ℝ) / (B : ℝ) * (d.1 : ℝ)| ≤ 1 := by
    rw [← hfirstScale]
    exact abs_le.mpr ⟨by linarith [hfirst.1], by linarith [hfirst.2]⟩
  have hsecondBound :
      |((j * d.2 / B : ℕ) : ℝ) - (j : ℝ) / (B : ℝ) * (d.2 : ℝ)| ≤ 1 := by
    rw [← hsecondScale]
    exact abs_le.mpr ⟨by linarith [hsecond.1], by linarith [hsecond.2]⟩
  have hsum :
      |((j * d.1 / B : ℕ) : ℝ) - (j : ℝ) / (B : ℝ) * (d.1 : ℝ)| +
        |((j * d.2 / B : ℕ) : ℝ) - (j : ℝ) / (B : ℝ) * (d.2 : ℝ)| ≤ 2 := by
    linarith [hfirstBound, hsecondBound]
  have hfirstCoord :
      |(u.1 : ℝ) + ((j * d.1 / B : ℕ) : ℝ) -
          ((u.1 : ℝ) + (j : ℝ) / (B : ℝ) * (d.1 : ℝ))| =
        |((j * d.1 / B : ℕ) : ℝ) - (j : ℝ) / (B : ℝ) * (d.1 : ℝ)| := by
    congr 1
    ring
  have hsecondCoord :
      |(u.2 : ℝ) + ((j * d.2 / B : ℕ) : ℝ) -
          ((u.2 : ℝ) + (j : ℝ) / (B : ℝ) * (d.2 : ℝ))| =
        |((j * d.2 / B : ℕ) : ℝ) - (j : ℝ) / (B : ℝ) * (d.2 : ℝ)| := by
    congr 1
    ring
  simp only [Prod.fst_add, Prod.snd_add, Int.cast_add, Int.cast_natCast]
  rw [hfirstCoord, hsecondCoord]
  exact hsum

/-- The actual floor increment differs from the scaled displacement by at most two in
real `l1` distance. -/
theorem floorSegment_increment_bounds (d : ℕ × ℕ) (B j : ℕ)
    (hB : 1 ≤ B) :
    let k : ℕ → ℕ × ℕ := fun n => (n * d.1 / B, n * d.2 / B)
    let Δ : ℕ → ℕ × ℕ := fun n =>
      ((k (n + 1)).1 - (k n).1, (k (n + 1)).2 - (k n).2)
    |((Δ j).1 : ℝ) - (d.1 : ℝ) / (B : ℝ)| +
        |((Δ j).2 : ℝ) - (d.2 : ℝ) / (B : ℝ)| ≤ 2 ∧
      (((d.1 + d.2 : ℕ) : ℝ) / (B : ℝ) - 2 ≤
        ((Δ j).1 : ℝ) + ((Δ j).2 : ℝ)) ∧
      (((Δ j).1 : ℝ) + ((Δ j).2 : ℝ) ≤
        ((d.1 + d.2 : ℕ) : ℝ) / (B : ℝ) + 2) := by
  dsimp only
  have hBPos : 0 < B := by omega
  have hfirst :
      |(((j + 1) * d.1 / B - j * d.1 / B : ℕ) : ℝ) -
        (d.1 : ℝ) / (B : ℝ)| ≤ 1 := by
    simpa only [Nat.succ_mul] using
      (nat_div_sub_increment_error (j * d.1) d.1 B hBPos)
  have hsecond :
      |(((j + 1) * d.2 / B - j * d.2 / B : ℕ) : ℝ) -
        (d.2 : ℝ) / (B : ℝ)| ≤ 1 := by
    simpa only [Nat.succ_mul] using
      (nat_div_sub_increment_error (j * d.2) d.2 B hBPos)
  have hscale : ((d.1 + d.2 : ℕ) : ℝ) / (B : ℝ) =
      (d.1 : ℝ) / (B : ℝ) + (d.2 : ℝ) / (B : ℝ) := by
    push_cast
    ring
  have hsum :
      |(((j + 1) * d.1 / B - j * d.1 / B : ℕ) : ℝ) -
          (d.1 : ℝ) / (B : ℝ)| +
        |(((j + 1) * d.2 / B - j * d.2 / B : ℕ) : ℝ) -
          (d.2 : ℝ) / (B : ℝ)| ≤ 2 := by
    linarith [hfirst, hsecond]
  have hforward1 :
      (((j + 1) * d.1 / B - j * d.1 / B : ℕ) : ℝ) -
          (d.1 : ℝ) / (B : ℝ) ≤
        |(((j + 1) * d.1 / B - j * d.1 / B : ℕ) : ℝ) -
          (d.1 : ℝ) / (B : ℝ)| := le_abs_self _
  have hforward2 :
      (((j + 1) * d.2 / B - j * d.2 / B : ℕ) : ℝ) -
          (d.2 : ℝ) / (B : ℝ) ≤
        |(((j + 1) * d.2 / B - j * d.2 / B : ℕ) : ℝ) -
          (d.2 : ℝ) / (B : ℝ)| := le_abs_self _
  have hbackward1 :
      (d.1 : ℝ) / (B : ℝ) -
          (((j + 1) * d.1 / B - j * d.1 / B : ℕ) : ℝ) ≤
        |(((j + 1) * d.1 / B - j * d.1 / B : ℕ) : ℝ) -
          (d.1 : ℝ) / (B : ℝ)| := by
    calc
      _ ≤ |(d.1 : ℝ) / (B : ℝ) -
          (((j + 1) * d.1 / B - j * d.1 / B : ℕ) : ℝ)| := le_abs_self _
      _ = _ := by rw [abs_sub_comm]
  have hbackward2 :
      (d.2 : ℝ) / (B : ℝ) -
          (((j + 1) * d.2 / B - j * d.2 / B : ℕ) : ℝ) ≤
        |(((j + 1) * d.2 / B - j * d.2 / B : ℕ) : ℝ) -
          (d.2 : ℝ) / (B : ℝ)| := by
    calc
      _ ≤ |(d.2 : ℝ) / (B : ℝ) -
          (((j + 1) * d.2 / B - j * d.2 / B : ℕ) : ℝ)| := le_abs_self _
      _ = _ := by rw [abs_sub_comm]
  refine ⟨?_, ?_, ?_⟩
  · simpa only using hsum
  · rw [hscale]
    linarith [hsum, hbackward1, hbackward2]
  · rw [hscale]
    linarith [hsum, hforward1, hforward2]

/-- The partition parameter is a point of the original unit interval. -/
theorem floorSegment_parameter (B j : ℕ) (hB : 1 ≤ B) (hj : j ≤ B) :
    0 ≤ (j : ℝ) / (B : ℝ) ∧ (j : ℝ) / (B : ℝ) ≤ 1 := by
  have hBReal : 0 < (B : ℝ) := by exact_mod_cast (show 0 < B by omega)
  constructor
  · positivity
  · apply (div_le_one₀ hBReal).2
    exact_mod_cast hj

/-- Every vertex of every actual piece path, including its terminal, lies within
the source's `|d|₁ / B + 4` distance of the corresponding segment point. -/
theorem floorSegment_path_vertex_distance (u : Lattice) (d : ℕ × ℕ)
    (B j : ℕ) (hB : 1 ≤ B) (_hj : j < B) :
    let k : ℕ → ℕ × ℕ := fun n => (n * d.1 / B, n * d.2 / B)
    let u' : ℕ → Lattice := fun n =>
      u + (((k n).1 : ℤ), ((k n).2 : ℤ))
    let Δ : ℕ → ℕ × ℕ := fun n =>
      ((k (n + 1)).1 - (k n).1, (k (n + 1)).2 - (k n).2)
    ∀ (p : Path (u' j) (Δ j))
      (i : Fin ((Δ j).1 + (Δ j).2 + 1)),
      |((p.vertex i).1 : ℝ) -
          ((u.1 : ℝ) + (j : ℝ) / (B : ℝ) * (d.1 : ℝ))| +
        |((p.vertex i).2 : ℝ) -
          ((u.2 : ℝ) + (j : ℝ) / (B : ℝ) * (d.2 : ℝ))| ≤
        ((d.1 + d.2 : ℕ) : ℝ) / (B : ℝ) + 4 := by
  intro k u' Δ p i
  have hanchor := floorSegment_anchor_error u d B j hB
  have hincrement := floorSegment_increment_bounds d B j hB
  have hdisp := hincrement.2.2
  have hbox := Path.vertex_mem_Icc p i
  have hfirstLower : (u' j).1 ≤ (p.vertex i).1 := hbox.1.1
  have hsecondLower : (u' j).2 ≤ (p.vertex i).2 := hbox.1.2
  have hfirstUpper : (p.vertex i).1 ≤ (u' j).1 + ((Δ j).1 : ℤ) := by
    simpa only [Prod.fst_add] using hbox.2.1
  have hsecondUpper : (p.vertex i).2 ≤ (u' j).2 + ((Δ j).2 : ℤ) := by
    simpa only [Prod.snd_add] using hbox.2.2
  have hfirstNonneg : 0 ≤ ((p.vertex i).1 : ℝ) - ((u' j).1 : ℝ) := by
    exact_mod_cast (show 0 ≤ (p.vertex i).1 - (u' j).1 by omega)
  have hsecondNonneg : 0 ≤ ((p.vertex i).2 : ℝ) - ((u' j).2 : ℝ) := by
    exact_mod_cast (show 0 ≤ (p.vertex i).2 - (u' j).2 by omega)
  have hfirstDistance :
      |((p.vertex i).1 : ℝ) - ((u' j).1 : ℝ)| ≤ ((Δ j).1 : ℝ) := by
    rw [abs_of_nonneg hfirstNonneg]
    exact_mod_cast (show (p.vertex i).1 - (u' j).1 ≤ ((Δ j).1 : ℤ) by omega)
  have hsecondDistance :
      |((p.vertex i).2 : ℝ) - ((u' j).2 : ℝ)| ≤ ((Δ j).2 : ℝ) := by
    rw [abs_of_nonneg hsecondNonneg]
    exact_mod_cast (show (p.vertex i).2 - (u' j).2 ≤ ((Δ j).2 : ℤ) by omega)
  have hfirstTriangle :
      |((p.vertex i).1 : ℝ) -
          ((u.1 : ℝ) + (j : ℝ) / (B : ℝ) * (d.1 : ℝ))| ≤
        |((p.vertex i).1 : ℝ) - ((u' j).1 : ℝ)| +
          |((u' j).1 : ℝ) -
            ((u.1 : ℝ) + (j : ℝ) / (B : ℝ) * (d.1 : ℝ))| := by
    calc
      _ = |(((p.vertex i).1 : ℝ) - ((u' j).1 : ℝ)) +
          (((u' j).1 : ℝ) -
            ((u.1 : ℝ) + (j : ℝ) / (B : ℝ) * (d.1 : ℝ)))| := by
        congr 1
        ring
      _ ≤ _ := abs_add_le _ _
  have hsecondTriangle :
      |((p.vertex i).2 : ℝ) -
          ((u.2 : ℝ) + (j : ℝ) / (B : ℝ) * (d.2 : ℝ))| ≤
        |((p.vertex i).2 : ℝ) - ((u' j).2 : ℝ)| +
          |((u' j).2 : ℝ) -
            ((u.2 : ℝ) + (j : ℝ) / (B : ℝ) * (d.2 : ℝ))| := by
    calc
      _ = |(((p.vertex i).2 : ℝ) - ((u' j).2 : ℝ)) +
          (((u' j).2 : ℝ) -
            ((u.2 : ℝ) + (j : ℝ) / (B : ℝ) * (d.2 : ℝ)))| := by
        congr 1
        ring
      _ ≤ _ := abs_add_le _ _
  calc
    _ ≤ (|((p.vertex i).1 : ℝ) - ((u' j).1 : ℝ)| +
          |((p.vertex i).2 : ℝ) - ((u' j).2 : ℝ)|) +
        (|((u' j).1 : ℝ) -
          ((u.1 : ℝ) + (j : ℝ) / (B : ℝ) * (d.1 : ℝ))| +
        |((u' j).2 : ℝ) -
          ((u.2 : ℝ) + (j : ℝ) / (B : ℝ) * (d.2 : ℝ))|) := by
      linarith [hfirstTriangle, hsecondTriangle]
    _ ≤ ((Δ j).1 : ℝ) + ((Δ j).2 : ℝ) + 2 := by
      linarith [hfirstDistance, hsecondDistance, hanchor]
    _ ≤ ((d.1 + d.2 : ℕ) : ℝ) / (B : ℝ) + 4 := by
      linarith [hdisp]

end LPPDifferentiability
