/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Boundary limits for bounded rectangle coboundaries

The boundary term in the rectangle proof of Krengel, *Ergodic Theorems*,
§6.2, Theorem 2.8, pp. 205–206, vanishes after division by the square scale.
-/

public section

open Filter
open scoped BigOperators Topology

namespace ProbabilityBasics

-- The named parameter `hzero` is part of the shared theorem interface.
set_option linter.unusedVariables false in
/-- For a bounded auxiliary function, the sum of either coordinate coboundary
over a half-open rectangle is negligible at square scale. This is the boundary
step in Krengel, *Ergodic Theorems*, §6.2, Theorem 2.8, pp. 205–206. -/
theorem tendsto_prefix_rectangle_bounded_coboundary
    {Ω : Type*} (T : (ℤ × ℤ) → Ω → Ω)
    (hzero : ∀ s, T 0 s = s)
    (hadd : ∀ z w s, T (z + w) s = T z (T w s))
    (φ : Ω → ℝ) (M : ℝ) (hM : 0 ≤ M) (hφ : ∀ s, |φ s| ≤ M)
    (b : Fin 2 → ℝ) (hb : ∀ i, 0 < b i) (i : Fin 2) :
    let e : Fin 2 → ℤ × ℤ := fun j => if j = 0 then (1, 0) else (0, 1)
    let R : ℕ → Finset (ℤ × ℤ) := fun n =>
      (Finset.Ico (0 : ℤ) ((⌊(n : ℝ) * b 0⌋₊ : ℕ) : ℤ)).product
        (Finset.Ico (0 : ℤ) ((⌊(n : ℝ) * b 1⌋₊ : ℕ) : ℤ))
    ∀ s, Tendsto (fun n : ℕ =>
      (∑ z ∈ R n, (φ (T z s) - φ (T (e i) (T z s)))) / (n : ℝ)^2)
      atTop (𝓝 0) := by
  let e : Fin 2 → ℤ × ℤ := fun j => if j = 0 then (1, 0) else (0, 1)
  let R : ℕ → Finset (ℤ × ℤ) := fun n =>
    (Finset.Ico (0 : ℤ) ((⌊(n : ℝ) * b 0⌋₊ : ℕ) : ℤ)).product
      (Finset.Ico (0 : ℤ) ((⌊(n : ℝ) * b 1⌋₊ : ℕ) : ℤ))
  change ∀ s, Tendsto (fun n : ℕ =>
    (∑ z ∈ R n, (φ (T z s) - φ (T (e i) (T z s)))) / (n : ℝ)^2) atTop (𝓝 0)
  intro s
  let A : ℕ → ℕ := fun n => ⌊(n : ℝ) * b 0⌋₊
  let B : ℕ → ℕ := fun n => ⌊(n : ℝ) * b 1⌋₊

  -- Reindex a nonnegative integer interval by its natural-number range.
  have hsumIco (N : ℕ) (f : ℤ → ℝ) :
      (∑ x ∈ Finset.Ico (0 : ℤ) (N : ℤ), f x) =
        ∑ k ∈ Finset.range N, f (k : ℤ) := by
    rw [Int.Ico_eq_finset_map]
    simp

  -- Decompose the rectangle in either orientation, then reindex both sides.
  have hrectRows (A B : ℕ) (f : ℤ × ℤ → ℝ) :
      (∑ z ∈ (Finset.Ico (0 : ℤ) (A : ℤ)).product
          (Finset.Ico (0 : ℤ) (B : ℤ)), f z) =
        ∑ y ∈ Finset.range B, ∑ x ∈ Finset.range A,
          f ((x : ℤ), (y : ℤ)) := by
    calc
      _ = ∑ y ∈ Finset.Ico (0 : ℤ) (B : ℤ),
          ∑ x ∈ Finset.Ico (0 : ℤ) (A : ℤ), f (x, y) :=
            Finset.sum_product_right _ _ _
      _ = ∑ y ∈ Finset.range B,
          ∑ x ∈ Finset.Ico (0 : ℤ) (A : ℤ), f (x, (y : ℤ)) := by
            rw [hsumIco]
      _ = ∑ y ∈ Finset.range B, ∑ x ∈ Finset.range A,
          f ((x : ℤ), (y : ℤ)) := by
            apply Finset.sum_congr rfl
            intro y hy
            exact hsumIco A (fun x => f (x, (y : ℤ)))

  have hrectCols (A B : ℕ) (f : ℤ × ℤ → ℝ) :
      (∑ z ∈ (Finset.Ico (0 : ℤ) (A : ℤ)).product
          (Finset.Ico (0 : ℤ) (B : ℤ)), f z) =
        ∑ x ∈ Finset.range A, ∑ y ∈ Finset.range B,
          f ((x : ℤ), (y : ℤ)) := by
    calc
      _ = ∑ x ∈ Finset.Ico (0 : ℤ) (A : ℤ),
          ∑ y ∈ Finset.Ico (0 : ℤ) (B : ℤ), f (x, y) :=
            Finset.sum_product _ _ _
      _ = ∑ x ∈ Finset.range A,
          ∑ y ∈ Finset.Ico (0 : ℤ) (B : ℤ), f ((x : ℤ), y) := by
            rw [hsumIco]
      _ = ∑ x ∈ Finset.range A, ∑ y ∈ Finset.range B,
          f ((x : ℤ), (y : ℤ)) := by
            apply Finset.sum_congr rfl
            intro x hx
            exact hsumIco B (fun y => f ((x : ℤ), y))

  let G : ℕ → ℕ → ℝ := fun x y => φ (T ((x : ℤ), (y : ℤ)) s)

  -- Each translated summand is the next value along the selected coordinate.
  fin_cases i
  ·
    have hshift (z : ℤ × ℤ) :
        φ (T (1, 0) (T z s)) = φ (T (z + (1, 0)) s) := by
      rw [← hadd (1, 0) z s]
      congr 2
      exact add_comm _ _
    have hnext (x y : ℕ) :
        φ (T (1, 0) (T ((x : ℤ), (y : ℤ)) s)) = G (x + 1) y := by
      rw [hshift]
      simp [G, Nat.cast_add]

    have hboundary (n : ℕ) :
        (∑ z ∈ R n, (φ (T z s) - φ (T (e 0) (T z s)))) =
          ∑ y ∈ Finset.range (B n), (G 0 y - G (A n) y) := by
      change (∑ z ∈ (Finset.Ico (0 : ℤ) (A n : ℤ)).product
          (Finset.Ico (0 : ℤ) (B n : ℤ)), (φ (T z s) - φ (T (1, 0) (T z s)))) = _
      calc
        _ = ∑ y ∈ Finset.range (B n), ∑ x ∈ Finset.range (A n),
            (φ (T ((x : ℤ), (y : ℤ)) s) -
              φ (T (1, 0) (T ((x : ℤ), (y : ℤ)) s))) :=
          hrectRows (A n) (B n) (fun z => φ (T z s) - φ (T (1, 0) (T z s)))
        _ = ∑ y ∈ Finset.range (B n), ∑ x ∈ Finset.range (A n),
            (G x y - G (x + 1) y) := by
          apply Finset.sum_congr rfl
          intro y _hy
          apply Finset.sum_congr rfl
          intro x _hx
          exact congrArg (fun v : ℝ => G x y - v) (hnext x y)
        _ = ∑ y ∈ Finset.range (B n), (G 0 y - G (A n) y) := by
          apply Finset.sum_congr rfl
          intro y _hy
          exact Finset.sum_range_sub' (fun x => G x y) (A n)

    have hboundary_bound (n : ℕ) :
        |∑ z ∈ R n, (φ (T z s) - φ (T (e 0) (T z s)))| ≤
          2 * M * (B n : ℝ) := by
      rw [hboundary n]
      have hterm (y : ℕ) : |G 0 y - G (A n) y| ≤ 2 * M := by
        calc
          |G 0 y - G (A n) y| ≤ |G 0 y| + |G (A n) y| := abs_sub _ _
          _ ≤ M + M := add_le_add (hφ _) (hφ _)
          _ = 2 * M := by ring
      calc
        |∑ y ∈ Finset.range (B n), (G 0 y - G (A n) y)| ≤
            ∑ y ∈ Finset.range (B n), |G 0 y - G (A n) y| :=
              Finset.abs_sum_le_sum_abs _ _
        _ ≤ (Finset.range (B n)).card • (2 * M) :=
              Finset.sum_le_card_nsmul _ _ _ (by
                intro y hy
                exact hterm y)
        _ = 2 * M * (B n : ℝ) := by simp [Finset.card_range, nsmul_eq_mul, mul_comm]

    let C : ℝ := 2 * M * b 1
    have hlim : Tendsto (fun n : ℕ => C / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat C
    have hfrac (n : ℕ) (hn : 1 ≤ n) :
        |(∑ z ∈ R n, (φ (T z s) - φ (T (e 0) (T z s)))) / (n : ℝ) ^ 2| ≤
          C / (n : ℝ) := by
      have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hn)
      have hfloor : (B n : ℝ) ≤ (n : ℝ) * b 1 := by
        dsimp [B]
        exact Nat.floor_le (mul_nonneg (Nat.cast_nonneg n) (hb 1).le)
      have hnum := hboundary_bound n
      rw [abs_div, abs_of_nonneg (sq_nonneg (n : ℝ))]
      calc
        |∑ z ∈ R n, (φ (T z s) - φ (T (e 0) (T z s)))| / (n : ℝ) ^ 2 ≤
            (2 * M * (B n : ℝ)) / (n : ℝ) ^ 2 :=
              div_le_div_of_nonneg_right hnum (sq_nonneg (n : ℝ))
        _ ≤ (2 * M * ((n : ℝ) * b 1)) / (n : ℝ) ^ 2 := by
              apply div_le_div_of_nonneg_right _ (sq_nonneg (n : ℝ))
              exact mul_le_mul_of_nonneg_left hfloor (by positivity)
        _ = C / (n : ℝ) := by
              dsimp [C]
              field_simp [ne_of_gt hnR]
    have hlimNeg : Tendsto (fun n : ℕ => -(C / (n : ℝ))) atTop (𝓝 0) := by
      simpa only [neg_zero] using hlim.neg
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlimNeg hlim ?_ ?_
    · filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
      exact (abs_le.mp (hfrac n hn)).1
    · filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
      exact (abs_le.mp (hfrac n hn)).2
  ·
    have hshift (z : ℤ × ℤ) :
        φ (T (0, 1) (T z s)) = φ (T (z + (0, 1)) s) := by
      rw [← hadd (0, 1) z s]
      congr 2
      exact add_comm _ _
    have hnext (x y : ℕ) :
        φ (T (0, 1) (T ((x : ℤ), (y : ℤ)) s)) = G x (y + 1) := by
      rw [hshift]
      simp [G, Nat.cast_add]

    have hboundary (n : ℕ) :
        (∑ z ∈ R n, (φ (T z s) - φ (T (e 1) (T z s)))) =
          ∑ x ∈ Finset.range (A n), (G x 0 - G x (B n)) := by
      change (∑ z ∈ (Finset.Ico (0 : ℤ) (A n : ℤ)).product
          (Finset.Ico (0 : ℤ) (B n : ℤ)), (φ (T z s) - φ (T (0, 1) (T z s)))) = _
      calc
        _ = ∑ x ∈ Finset.range (A n), ∑ y ∈ Finset.range (B n),
            (φ (T ((x : ℤ), (y : ℤ)) s) -
              φ (T (0, 1) (T ((x : ℤ), (y : ℤ)) s))) :=
          hrectCols (A n) (B n) (fun z => φ (T z s) - φ (T (0, 1) (T z s)))
        _ = ∑ x ∈ Finset.range (A n), ∑ y ∈ Finset.range (B n),
            (G x y - G x (y + 1)) := by
          apply Finset.sum_congr rfl
          intro x _hx
          apply Finset.sum_congr rfl
          intro y _hy
          exact congrArg (fun v : ℝ => G x y - v) (hnext x y)
        _ = ∑ x ∈ Finset.range (A n), (G x 0 - G x (B n)) := by
          apply Finset.sum_congr rfl
          intro x _hx
          exact Finset.sum_range_sub' (fun y => G x y) (B n)

    have hboundary_bound (n : ℕ) :
        |∑ z ∈ R n, (φ (T z s) - φ (T (e 1) (T z s)))| ≤
          2 * M * (A n : ℝ) := by
      rw [hboundary n]
      have hterm (x : ℕ) : |G x 0 - G x (B n)| ≤ 2 * M := by
        calc
          |G x 0 - G x (B n)| ≤ |G x 0| + |G x (B n)| := abs_sub _ _
          _ ≤ M + M := add_le_add (hφ _) (hφ _)
          _ = 2 * M := by ring
      calc
        |∑ x ∈ Finset.range (A n), (G x 0 - G x (B n))| ≤
            ∑ x ∈ Finset.range (A n), |G x 0 - G x (B n)| :=
              Finset.abs_sum_le_sum_abs _ _
        _ ≤ (Finset.range (A n)).card • (2 * M) :=
              Finset.sum_le_card_nsmul _ _ _ (by
                intro x hx
                exact hterm x)
        _ = 2 * M * (A n : ℝ) := by simp [Finset.card_range, nsmul_eq_mul, mul_comm]

    let C : ℝ := 2 * M * b 0
    have hlim : Tendsto (fun n : ℕ => C / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat C
    have hfrac (n : ℕ) (hn : 1 ≤ n) :
        |(∑ z ∈ R n, (φ (T z s) - φ (T (e 1) (T z s)))) / (n : ℝ) ^ 2| ≤
          C / (n : ℝ) := by
      have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hn)
      have hfloor : (A n : ℝ) ≤ (n : ℝ) * b 0 := by
        dsimp [A]
        exact Nat.floor_le (mul_nonneg (Nat.cast_nonneg n) (hb 0).le)
      have hnum := hboundary_bound n
      rw [abs_div, abs_of_nonneg (sq_nonneg (n : ℝ))]
      calc
        |∑ z ∈ R n, (φ (T z s) - φ (T (e 1) (T z s)))| / (n : ℝ) ^ 2 ≤
            (2 * M * (A n : ℝ)) / (n : ℝ) ^ 2 :=
              div_le_div_of_nonneg_right hnum (sq_nonneg (n : ℝ))
        _ ≤ (2 * M * ((n : ℝ) * b 0)) / (n : ℝ) ^ 2 := by
              apply div_le_div_of_nonneg_right _ (sq_nonneg (n : ℝ))
              exact mul_le_mul_of_nonneg_left hfloor (by positivity)
        _ = C / (n : ℝ) := by
              dsimp [C]
              field_simp [ne_of_gt hnR]
    have hlimNeg : Tendsto (fun n : ℕ => -(C / (n : ℝ))) atTop (𝓝 0) := by
      simpa only [neg_zero] using hlim.neg
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlimNeg hlim ?_ ?_
    · filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
      exact (abs_le.mp (hfrac n hn)).1
    · filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
      exact (abs_le.mp (hfrac n hn)).2

end ProbabilityBasics
