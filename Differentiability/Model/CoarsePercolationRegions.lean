/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.Lattice
public import Mathlib.Data.Nat.Dist
import Mathlib.Tactic

/-! Deterministic overlap and separation bounds for the closed coarse regions. -/

public section

namespace LPPDifferentiability

private theorem nat_dist_le_of_two_add_bounds {x y k : ℕ}
    (hxy : x ≤ y + k) (hyx : y ≤ x + k) : Nat.dist x y ≤ k := by
  unfold Nat.dist
  omega

private theorem nat_layer_dist_le_one_of_common_closed_level
    (i j H : ℕ) (hH : 1 ≤ H) (level : ℤ)
    (hilow : ((i * H : ℕ) : ℤ) ≤ level)
    (hihigh : level ≤ (((i + 1) * H : ℕ) : ℤ))
    (hjlow : ((j * H : ℕ) : ℤ) ≤ level)
    (hjhigh : level ≤ (((j + 1) * H : ℕ) : ℤ)) : Nat.dist i j ≤ 1 := by
  have hij : i ≤ j + 1 := by
    by_contra h
    have htwo : j + 2 ≤ i := by omega
    have hmul : (j + 2) * H ≤ i * H := Nat.mul_le_mul_right H htwo
    have hsplit : (j + 2) * H = (j + 1) * H + H := by
      calc
        (j + 2) * H = (j + 1 + 1) * H := by congr 1
        _ = (j + 1) * H + 1 * H := Nat.add_mul _ _ _
        _ = (j + 1) * H + H := by simp
    have hgap : (j + 1) * H + 1 ≤ i * H := by omega
    have hgapInt : (((j + 1) * H : ℕ) : ℤ) + 1 ≤ ((i * H : ℕ) : ℤ) := by
      exact_mod_cast hgap
    omega
  have hji : j ≤ i + 1 := by
    by_contra h
    have htwo : i + 2 ≤ j := by omega
    have hmul : (i + 2) * H ≤ j * H := Nat.mul_le_mul_right H htwo
    have hsplit : (i + 2) * H = (i + 1) * H + H := by
      calc
        (i + 2) * H = (i + 1 + 1) * H := by congr 1
        _ = (i + 1) * H + 1 * H := Nat.add_mul _ _ _
        _ = (i + 1) * H + H := by simp
    have hgap : (i + 1) * H + 1 ≤ j * H := by omega
    have hgapInt : (((i + 1) * H : ℕ) : ℤ) + 1 ≤ ((j * H : ℕ) : ℤ) := by
      exact_mod_cast hgap
    omega
  exact nat_dist_le_of_two_add_bounds hij hji

/-- A common point in two closed coarse regions bounds both site coordinates;
sites whose sup-distance exceeds ten have disjoint regions. The region is
defined locally in the statement and is shared by both conclusions. -/
theorem coarse_percolation_regions_radius_ten
    (a σ S : ℝ) (H : ℕ) (hH : 1 ≤ H) (hS : 0 < S)
    (hσ : σ = 1 ∨ σ = -1) :
    let t : ℕ × ℕ → ℕ := fun v => v.1 + v.2
    let q : ℕ × ℕ → ℕ := fun v => v.1 + 2 * v.2
    let R : ℕ × ℕ → Set Lattice := fun v =>
      {z | ((t v * H : ℕ) : ℤ) ≤ z.1 + z.2 ∧
        z.1 + z.2 ≤ (((t v + 1) * H : ℕ) : ℤ) ∧
        |(1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ) - σ * (q v : ℝ) * S| ≤ 4 * S}
    (∀ u v, (R u ∩ R v).Nonempty →
      Nat.dist (t u) (t v) ≤ 1 ∧
        Nat.dist u.2 v.2 ≤ 9 ∧ Nat.dist u.1 v.1 ≤ 10) ∧
    (∀ u v, 10 < Nat.dist u.1 v.1 ∨ 10 < Nat.dist u.2 v.2 →
      Disjoint (R u) (R v)) := by
  classical
  intro t q R
  have hOverlapBounds : ∀ u v, (R u ∩ R v).Nonempty →
      Nat.dist (t u) (t v) ≤ 1 ∧
        Nat.dist u.2 v.2 ≤ 9 ∧ Nat.dist u.1 v.1 ≤ 10 := by
    intro u v hOverlap
    obtain ⟨z, hz⟩ := hOverlap
    change z ∈ R u ∧ z ∈ R v at hz
    rcases hz with ⟨hu, hv⟩
    change ((t u * H : ℕ) : ℤ) ≤ z.1 + z.2 ∧
      z.1 + z.2 ≤ (((t u + 1) * H : ℕ) : ℤ) ∧
      |(1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ) - σ * (q u : ℝ) * S| ≤ 4 * S at hu
    change ((t v * H : ℕ) : ℤ) ≤ z.1 + z.2 ∧
      z.1 + z.2 ≤ (((t v + 1) * H : ℕ) : ℤ) ∧
      |(1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ) - σ * (q v : ℝ) * S| ≤ 4 * S at hv
    have ht : Nat.dist (t u) (t v) ≤ 1 :=
      nat_layer_dist_le_one_of_common_closed_level (t u) (t v) H hH
        (z.1 + z.2) hu.1 hu.2.1 hv.1 hv.2.1
    have hqU : q u = t u + u.2 := by dsimp [q, t]; omega
    have hqV : q v = t v + v.2 := by dsimp [q, t]; omega
    let A : ℝ := (1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ)
    have hCenters : |σ * ((q u : ℝ) - (q v : ℝ)) * S| ≤ 8 * S := by
      have hCenterEq : σ * ((q u : ℝ) - (q v : ℝ)) * S =
          (A - σ * (q v : ℝ) * S) - (A - σ * (q u : ℝ) * S) := by
        dsimp [A]
        ring
      calc
        _ = |(A - σ * (q v : ℝ) * S) - (A - σ * (q u : ℝ) * S)| := by
          rw [hCenterEq]
        _ ≤ |A - σ * (q v : ℝ) * S| + |A - σ * (q u : ℝ) * S| := by
          simpa only [sub_zero, zero_sub, abs_neg] using
            (abs_sub_le (A - σ * (q v : ℝ) * S) 0 (A - σ * (q u : ℝ) * S))
        _ ≤ 4 * S + 4 * S := add_le_add hv.2.2 hu.2.2
        _ = 8 * S := by ring
    have hσabs : |σ| = 1 := by
      rcases hσ with hσ | hσ <;> simp [hσ]
    have hFactor : |σ * ((q u : ℝ) - (q v : ℝ)) * S| =
        |(q u : ℝ) - (q v : ℝ)| * S := by
      rw [abs_mul, abs_mul, hσabs, abs_of_pos hS]
      ring
    have hScale : |(q u : ℝ) - (q v : ℝ)| * S ≤ 8 * S := by
      calc
        _ = |σ * ((q u : ℝ) - (q v : ℝ)) * S| := hFactor.symm
        _ ≤ 8 * S := hCenters
    have hqAbs : |(q u : ℝ) - (q v : ℝ)| ≤ 8 :=
      le_of_mul_le_mul_right hScale hS
    have hqUvReal : (q u : ℝ) ≤ (q v : ℝ) + 8 := by
      have := (abs_le.mp hqAbs).2
      linarith
    have hqVuReal : (q v : ℝ) ≤ (q u : ℝ) + 8 := by
      have := (abs_le.mp hqAbs).1
      linarith
    have hqUv : q u ≤ q v + 8 := by exact_mod_cast hqUvReal
    have hqVu : q v ≤ q u + 8 := by exact_mod_cast hqVuReal
    have hq : Nat.dist (q u) (q v) ≤ 8 :=
      nat_dist_le_of_two_add_bounds hqUv hqVu
    have hSecond : Nat.dist u.2 v.2 ≤ 9 := by
      calc
        Nat.dist u.2 v.2 = Nat.dist (t u + u.2) (t u + v.2) := by
          rw [Nat.dist_add_add_left]
        _ ≤ Nat.dist (t u + u.2) (t v + v.2) +
            Nat.dist (t v + v.2) (t u + v.2) := Nat.dist.triangle_inequality _ _ _
        _ = Nat.dist (t u + u.2) (t v + v.2) + Nat.dist (t v) (t u) := by
          rw [Nat.dist_add_add_right]
        _ = Nat.dist (q u) (q v) + Nat.dist (t u) (t v) := by
          rw [hqU, hqV]
          exact congrArg (fun d => Nat.dist (t u + u.2) (t v + v.2) + d)
            (Nat.dist_comm (t v) (t u))
        _ ≤ 8 + 1 := Nat.add_le_add hq ht
        _ = 9 := by norm_num
    have hFirst : Nat.dist u.1 v.1 ≤ 10 := by
      calc
        Nat.dist u.1 v.1 = Nat.dist (u.1 + u.2) (v.1 + u.2) := by
          rw [Nat.dist_add_add_right]
        _ ≤ Nat.dist (u.1 + u.2) (v.1 + v.2) +
            Nat.dist (v.1 + v.2) (v.1 + u.2) := Nat.dist.triangle_inequality _ _ _
        _ = Nat.dist (t u) (t v) + Nat.dist u.2 v.2 := by
          simp [t, Nat.dist_add_add_left, Nat.dist_comm]
        _ ≤ 1 + 9 := Nat.add_le_add ht hSecond
        _ = 10 := by norm_num
    exact ⟨ht, hSecond, hFirst⟩
  refine ⟨hOverlapBounds, ?_⟩
  intro u v hSeparated
  apply Set.disjoint_left.mpr
  intro z hu hv
  change ((t u * H : ℕ) : ℤ) ≤ z.1 + z.2 ∧
    z.1 + z.2 ≤ (((t u + 1) * H : ℕ) : ℤ) ∧
    |(1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ) - σ * (q u : ℝ) * S| ≤ 4 * S at hu
  change ((t v * H : ℕ) : ℤ) ≤ z.1 + z.2 ∧
    z.1 + z.2 ≤ (((t v + 1) * H : ℕ) : ℤ) ∧
    |(1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ) - σ * (q v : ℝ) * S| ≤ 4 * S at hv
  have hBounds := hOverlapBounds u v ⟨z, ⟨hu, hv⟩⟩
  obtain ⟨_, hSecond, hFirst⟩ := hBounds
  rcases hSeparated with hFirstSeparated | hSecondSeparated
  · omega
  · omega
