/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Bernoulli scale bounds

Direct arithmetic for the reciprocal-power scale and covering count in the
proof of Martin (2002), Proposition 2.2, specialized to dimension two.
-/

public section

namespace LPPDifferentiability

/-- The natural ceiling of the reciprocal square-root scale is positive. -/
theorem bernoulli_scale_positive (p : ℝ) (hp : 0 < p) :
    1 ≤ Nat.ceil (1 / Real.sqrt p) := by
  exact Nat.one_le_ceil_iff.mpr (by positivity)

/-- The scale ceiling is at most the length in the large-scale regime. -/
theorem bernoulli_scale_le_n (n : ℕ) (p : ℝ) (hp : 0 < p)
    (ha : 1 < (n : ℝ) * Real.sqrt p) :
    Nat.ceil (1 / Real.sqrt p) ≤ n := by
  have hs : 0 < Real.sqrt p := by positivity
  have hx : 1 / Real.sqrt p < (n : ℝ) := by
    apply (div_lt_iff₀ hs).2
    simpa only [one_mul] using ha
  exact Nat.ceil_le.2 hx.le

/-- The ceiling is bounded by twice the reciprocal square-root scale. -/
theorem bernoulli_scale_upper (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    (Nat.ceil (1 / Real.sqrt p) : ℝ) ≤ 2 / Real.sqrt p := by
  have hs : 0 < Real.sqrt p := by positivity
  have hs1 : Real.sqrt p ≤ 1 := Real.sqrt_le_one.mpr hp1
  have hinv : 1 ≤ 1 / Real.sqrt p := (one_le_div₀ hs).2 hs1
  calc
    (Nat.ceil (1 / Real.sqrt p) : ℝ) ≤ 1 / Real.sqrt p + 1 :=
      (Nat.ceil_lt_add_one (by positivity)).le
    _ ≤ 1 / Real.sqrt p + 1 / Real.sqrt p := by linarith
    _ = 2 / Real.sqrt p := by ring

/-- The cell side length factor is at most nine reciprocal square roots. -/
theorem bernoulli_cell_size_bound (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    4 * (Nat.ceil (1 / Real.sqrt p) : ℝ) + 1 ≤ 9 / Real.sqrt p := by
  have hs : 0 < Real.sqrt p := by positivity
  have hs1 : Real.sqrt p ≤ 1 := Real.sqrt_le_one.mpr hp1
  have hinv : 1 ≤ 1 / Real.sqrt p := (one_le_div₀ hs).2 hs1
  have hceil := bernoulli_scale_upper p hp hp1
  calc
    4 * (Nat.ceil (1 / Real.sqrt p) : ℝ) + 1 ≤
        4 * (2 / Real.sqrt p) + 1 := by nlinarith
    _ ≤ 4 * (2 / Real.sqrt p) + 1 / Real.sqrt p := by linarith
    _ = 9 / Real.sqrt p := by ring

/-- The actual natural-division radius is at most twice n times sqrt p. -/
theorem bernoulli_radius_bound (n : ℕ) (p : ℝ) (hn : 1 ≤ n) (hp : 0 < p) :
    ((2 * n / Nat.ceil (1 / Real.sqrt p) : ℕ) : ℝ) ≤
      2 * (n : ℝ) * Real.sqrt p := by
  let l : ℕ := Nat.ceil (1 / Real.sqrt p)
  let r : ℕ := 2 * n / l
  have hlN : 1 ≤ l := by
    dsimp [l]
    exact bernoulli_scale_positive p hp
  have hlposN : 0 < l := lt_of_lt_of_le Nat.zero_lt_one hlN
  have hlpos : 0 < (l : ℝ) := by exact_mod_cast hlposN
  have hspos : 0 < Real.sqrt p := by positivity
  have hlower : 1 / Real.sqrt p ≤ (l : ℝ) := by
    dsimp [l]
    exact Nat.le_ceil _
  have hmul := mul_le_mul_of_nonneg_right hlower (Real.sqrt_nonneg p)
  have hinv_mul : 1 ≤ Real.sqrt p * (l : ℝ) := by
    calc
      1 = (1 / Real.sqrt p) * Real.sqrt p := by field_simp [ne_of_gt hspos]
      _ ≤ (l : ℝ) * Real.sqrt p := hmul
      _ = Real.sqrt p * (l : ℝ) := by ring
  have hinv : 1 / (l : ℝ) ≤ Real.sqrt p := (div_le_iff₀ hlpos).2 hinv_mul
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hfactor : 0 ≤ (2 : ℝ) * (n : ℝ) := mul_nonneg (by norm_num) hnpos.le
  have hdiv_nat : r * l ≤ 2 * n := by
    dsimp [r]
    exact Nat.div_mul_le_self _ _
  have hdiv : (r : ℝ) ≤ (2 : ℝ) * (n : ℝ) / (l : ℝ) := by
    apply (le_div_iff₀ hlpos).2
    exact_mod_cast hdiv_nat
  calc
    ((2 * n / Nat.ceil (1 / Real.sqrt p) : ℕ) : ℝ) = (r : ℝ) := by rfl
    _ ≤ (2 : ℝ) * (n : ℝ) / (l : ℝ) := hdiv
    _ = (2 : ℝ) * (n : ℝ) * (1 / (l : ℝ)) := by ring
    _ ≤ (2 : ℝ) * (n : ℝ) * Real.sqrt p :=
      mul_le_mul_of_nonneg_left hinv hfactor
    _ = 2 * (n : ℝ) * Real.sqrt p := by ring

/-- The covering count of the greedy-lattice-animal argument has the dimension-two constant 243. -/
theorem bernoulli_cover_count_bound (n : ℕ) (p : ℝ) (hn : 1 ≤ n)
    (hp : 0 < p) (hp1 : p ≤ 1) (ha : 1 < (n : ℝ) * Real.sqrt p) :
    let l : ℕ := Nat.ceil (1 / Real.sqrt p)
    let r : ℕ := 2 * n / l
    ((r : ℝ) + 1) * (4 * (l : ℝ) + 1) ^ 2 ≤
      243 * ((n : ℝ) * Real.sqrt p) / p := by
  let l : ℕ := Nat.ceil (1 / Real.sqrt p)
  let r : ℕ := 2 * n / l
  change ((r : ℝ) + 1) * (4 * (l : ℝ) + 1) ^ 2 ≤
    243 * ((n : ℝ) * Real.sqrt p) / p
  have hradius : (r : ℝ) ≤ 2 * ((n : ℝ) * Real.sqrt p) := by
    dsimp [r, l]
    calc
      ((2 * n / Nat.ceil (1 / Real.sqrt p) : ℕ) : ℝ) ≤
          2 * (n : ℝ) * Real.sqrt p :=
        bernoulli_radius_bound n p hn hp
      _ = 2 * ((n : ℝ) * Real.sqrt p) := by ring
  have hplus :
      (r : ℝ) + 1 ≤ 3 * ((n : ℝ) * Real.sqrt p) := by
    linarith [hradius, ha]
  have hcell :
      4 * (l : ℝ) + 1 ≤ 9 / Real.sqrt p := by
    dsimp [l]
    exact bernoulli_cell_size_bound p hp hp1
  have hcell_sq :
      (4 * (l : ℝ) + 1) ^ 2 ≤ 81 / p := by
    have hsquare :
        (4 * (l : ℝ) + 1) ^ 2 ≤ (9 / Real.sqrt p) ^ 2 :=
      (sq_le_sq₀ (by positivity) (by positivity)).2 hcell
    have hidentity : (9 / Real.sqrt p) ^ 2 = 81 / p := by
      rw [div_pow, Real.sq_sqrt hp.le]
      norm_num
    exact hsquare.trans_eq hidentity
  calc
    ((r : ℝ) + 1) * (4 * (l : ℝ) + 1) ^ 2 ≤
        (3 * ((n : ℝ) * Real.sqrt p)) * (81 / p) :=
      calc
        ((r : ℝ) + 1) * (4 * (l : ℝ) + 1) ^ 2 ≤
            (3 * ((n : ℝ) * Real.sqrt p)) * (4 * (l : ℝ) + 1) ^ 2 :=
          mul_le_mul_of_nonneg_right hplus (sq_nonneg _)
        _ ≤ (3 * ((n : ℝ) * Real.sqrt p)) * (81 / p) :=
          mul_le_mul_of_nonneg_left hcell_sq (by positivity)
    _ = 243 * ((n : ℝ) * Real.sqrt p) / p := by ring

/-- In the small-scale regime, the quadratic Bernoulli term is bounded linearly. -/
theorem bernoulli_small_scale_square_bound (n : ℕ) (p : ℝ) (hn : 1 ≤ n)
    (hp : 0 ≤ p) (ha : (n : ℝ) * Real.sqrt p ≤ 1) :
    (2 * (n : ℝ)) ^ 2 * p ≤ 4 * (n : ℝ) * Real.sqrt p := by
  let x : ℝ := (n : ℝ) * Real.sqrt p
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hxnonneg : 0 ≤ x := by
    dsimp [x]
    exact mul_nonneg hnpos.le (Real.sqrt_nonneg p)
  have hxle : x ≤ 1 := by
    dsimp [x]
    exact ha
  have hx_sq : x ^ 2 ≤ x := by
    calc
      x ^ 2 = x * x := by ring
      _ ≤ 1 * x := mul_le_mul_of_nonneg_right hxle hxnonneg
      _ = x := by ring
  have hsquare : (Real.sqrt p) ^ 2 = p := Real.sq_sqrt hp
  have heq : (2 * (n : ℝ)) ^ 2 * p = 4 * x ^ 2 := by
    dsimp [x]
    calc
      (2 * (n : ℝ)) ^ 2 * p = 4 * (n : ℝ) ^ 2 * p := by ring
      _ = 4 * ((n : ℝ) * Real.sqrt p) ^ 2 := by
        rw [mul_pow, hsquare]
        ring
  calc
    (2 * (n : ℝ)) ^ 2 * p = 4 * x ^ 2 := heq
    _ ≤ 4 * x := mul_le_mul_of_nonneg_left hx_sq (by norm_num)
    _ = 4 * (n : ℝ) * Real.sqrt p := by dsimp [x]; ring

end LPPDifferentiability

