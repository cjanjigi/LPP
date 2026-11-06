/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Analysis.GridScaleSums
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Grid scales: the corrected fine-scale count

Scalar arithmetic for the corrected count of fine-scale staircases, as in (5.15), (5.27) and
(5.32) to (5.36) of the differentiability preprint. The corrected count replaces an earlier
count `w + 1`.

Here `s = 2 ^ k`, `w_j = 2 ^ (k - j)`, `l_j = 2 ^ (m - 4 j - 1)` (natural subtraction), and the
constant `c` is the constant `c_*` of the preprint. The results reuse the lemmas of
`LPPDifferentiability.Analysis.GridScaleSums`, which this module imports.

## References

- C. Janjigian, F. Rassoul-Agha and T. Seppäläinen, *Differentiability of the shape function in
  the planar corner growth model*, preprint.
-/

public section

open Filter Topology

namespace LPPDifferentiability

/-- At a fine scale, as in (5.15) of the differentiability preprint, `l + 1 ≤ 8 c j ^ 2 w + 1`
and `c j ^ 2 w ^ 2 ≥ w + 1` give the staircase count bound `(l + 1) w + 1 ≤ 9 c j ^ 2 w ^ 2`. -/
theorem grid_fine_count_le {l w j : ℕ} {c : ℝ} (hc : 1 ≤ c) (hj : 1 ≤ j) (hw : 2 ≤ w)
    (hfine : (l : ℝ) < 8 * c * j ^ 2 * w) : ((l + 1) * w + 1 : ℝ) ≤ 9 * c * j ^ 2 * w ^ 2 := by
  have hw' : (2 : ℝ) ≤ w := by exact_mod_cast hw
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hw0 : (0 : ℝ) ≤ w := by linarith
  have hj2 : (1 : ℝ) ≤ (j : ℝ) ^ 2 := one_le_pow₀ hj'
  have hcj : 1 ≤ c * (j : ℝ) ^ 2 := by nlinarith
  have hl : (l : ℝ) + 1 ≤ 8 * c * j ^ 2 * w + 1 := by linarith
  have hw2 : (w : ℝ) + 1 ≤ (w : ℝ) ^ 2 := by nlinarith
  have hcw : (w : ℝ) ^ 2 ≤ c * (j : ℝ) ^ 2 * w ^ 2 := by nlinarith
  calc ((l : ℝ) + 1) * w + 1 ≤ (8 * c * j ^ 2 * w + 1) * w + 1 := by gcongr
    _ = 8 * c * j ^ 2 * w ^ 2 + (w + 1) := by ring
    _ ≤ 8 * c * j ^ 2 * w ^ 2 + c * (j : ℝ) ^ 2 * w ^ 2 := by linarith
    _ = 9 * c * j ^ 2 * w ^ 2 := by ring

/-- At every scale `j ≤ k` (with the bound (5.6) of the differentiability preprint, and the
fine term of (5.35)), the fine term satisfies
`9 c j ^ 2 2 ^ (5 j) w_j ^ 2 = 9 c j ^ 2 2 ^ (3 j + 2 k) ≤ 9 c k ^ 2 2 ^ (5 k)`. The preprint
gets `j ≤ k` from `4 j ≤ m + 3 ≤ 3 k + 3` and `k ≥ 3`; here `j ≤ k` is the input `hjk`. -/
theorem grid_fine_term_le_nine {m k j jstar : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (_hjstar : jstar = ⌈((m : ℝ) - 1) / 4⌉₊) (hjk : j ≤ k) (_hm : m ≤ 3 * k) (_hk : 3 ≤ k)
    (_hj : j ≤ jstar) :
    9 * c * j ^ 2 * 2 ^ (5 * j) * ((2 : ℝ) ^ (k - j)) ^ 2 ≤
      9 * c * k ^ 2 * ((2 : ℝ) ^ k) ^ 5 := by
  have hj0 : (j : ℝ) ≤ k := by exact_mod_cast hjk
  have h9 : 0 ≤ 9 * c := by linarith
  have hexp : (2 : ℝ) ^ (5 * j) * ((2 : ℝ) ^ (k - j)) ^ 2 = (2 : ℝ) ^ (5 * j + 2 * (k - j)) := by
    rw [← pow_mul, ← pow_add, mul_comm (k - j) 2]
  have hle : 5 * j + 2 * (k - j) ≤ 5 * k := by omega
  have hpow : (2 : ℝ) ^ (5 * j + 2 * (k - j)) ≤ (2 : ℝ) ^ (5 * k) :=
    pow_le_pow_right₀ (by norm_num) hle
  have hsq : (j : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hj0 2
  calc 9 * c * j ^ 2 * 2 ^ (5 * j) * ((2 : ℝ) ^ (k - j)) ^ 2
      = 9 * c * j ^ 2 * ((2 : ℝ) ^ (5 * j) * ((2 : ℝ) ^ (k - j)) ^ 2) := by ring
    _ = 9 * c * j ^ 2 * (2 : ℝ) ^ (5 * j + 2 * (k - j)) := by rw [hexp]
    _ ≤ 9 * c * k ^ 2 * (2 : ℝ) ^ (5 * k) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hsq h9) hpow (by positivity)
          (mul_nonneg h9 (sq_nonneg _))
    _ = 9 * c * k ^ 2 * ((2 : ℝ) ^ k) ^ 5 := by ring

open scoped Classical in
/-- With the same hypotheses as `grid_staircase_sum_le`, the coarse terms (bounded by
`grid_coarse_term_le`, as in (5.34) of the differentiability preprint) and the fine terms
(bounded by `grid_fine_term_le_nine`, as in (5.35)) add up to at most `(60 + 9 c) k ^ 3 s ^ 5`,
because there are at most `k` scales (see (5.32) to (5.36)). -/
theorem grid_staircase_sum_le_nine {m k k0 J jstar : ℕ} {c : ℝ}
    (hjstar : jstar = ⌈((m : ℝ) - 1) / 4⌉₊) (hm : m ≤ 3 * k) (hk : 4 * k0 + 3 ≤ k)
    (hk0 : 0 < k0) (hJ : 1 ≤ J) (hc : 1 ≤ c) :
    (∑ j ∈ (Finset.Icc J jstar).filter
        (fun j : ℕ => 8 * (c * (j : ℝ) ^ 2 * 2 ^ (k - j)) ≤ (2 : ℝ) ^ (m - 4 * j - 1)),
      60 * (j : ℝ) ^ 2 * 2 ^ (5 * j) * ((2 : ℝ) ^ (k - j)) ^ 2) +
    (∑ j ∈ (Finset.Icc J jstar).filter
        (fun j : ℕ => ¬ 8 * (c * (j : ℝ) ^ 2 * 2 ^ (k - j)) ≤ (2 : ℝ) ^ (m - 4 * j - 1)),
      9 * c * (j : ℝ) ^ 2 * 2 ^ (5 * j) * ((2 : ℝ) ^ (k - j)) ^ 2) ≤
    (60 + 9 * c) * (k : ℝ) ^ 3 * ((2 : ℝ) ^ k) ^ 5 := by
  have hjs : jstar ≤ k := (grid_scale_index_bounds hjstar hm hk hk0 le_rfl).1
  have hk3 : 3 ≤ k := by omega
  have hc0 : (0 : ℝ) ≤ c := by linarith
  have h9 : 0 ≤ 9 * c := by linarith
  have hcard : (Finset.Icc J jstar).card ≤ k := by rw [Nat.card_Icc]; omega
  have hs1 : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have h1 : (∑ j ∈ (Finset.Icc J jstar).filter
        (fun j : ℕ => 8 * (c * (j : ℝ) ^ 2 * 2 ^ (k - j)) ≤ (2 : ℝ) ^ (m - 4 * j - 1)),
      60 * (j : ℝ) ^ 2 * 2 ^ (5 * j) * ((2 : ℝ) ^ (k - j)) ^ 2) ≤
      k * (60 * (k : ℝ) ^ 2 * ((2 : ℝ) ^ k) ^ 5) := by
    refine (Finset.sum_le_card_nsmul _ _ (60 * (k : ℝ) ^ 2 * ((2 : ℝ) ^ k) ^ 5) fun j hj => ?_).trans ?_
    · obtain ⟨hj1, hcl⟩ := Finset.mem_filter.1 hj
      obtain ⟨hJj, hjj⟩ := Finset.mem_Icc.1 hj1
      have hj1' : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hJ.trans hJj
      have hj2 : (1 : ℝ) ≤ (j : ℝ) ^ 2 := one_le_pow₀ hj1'
      have hnat := grid_coarse_term_le (hjj.trans hjs) hm (by nlinarith) hcl
      have hreal : 60 * (j : ℝ) ^ 2 * 2 ^ (5 * j) * ((2 : ℝ) ^ (k - j)) ^ 2 ≤
          60 * (k : ℝ) ^ 2 * ((2 : ℝ) ^ k) ^ 4 := by
        exact_mod_cast hnat
      have h4 : ((2 : ℝ) ^ k) ^ 4 ≤ ((2 : ℝ) ^ k) ^ 5 := pow_le_pow_right₀ hs1 (by norm_num)
      exact hreal.trans (mul_le_mul_of_nonneg_left h4 (by positivity))
    · rw [nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast (Finset.card_filter_le _ _).trans hcard) (by positivity)
  have h2 : (∑ j ∈ (Finset.Icc J jstar).filter
        (fun j : ℕ => ¬ 8 * (c * (j : ℝ) ^ 2 * 2 ^ (k - j)) ≤ (2 : ℝ) ^ (m - 4 * j - 1)),
      9 * c * (j : ℝ) ^ 2 * 2 ^ (5 * j) * ((2 : ℝ) ^ (k - j)) ^ 2) ≤
      k * (9 * c * (k : ℝ) ^ 2 * ((2 : ℝ) ^ k) ^ 5) := by
    refine (Finset.sum_le_card_nsmul _ _ (9 * c * (k : ℝ) ^ 2 * ((2 : ℝ) ^ k) ^ 5)
      fun j hj => ?_).trans ?_
    · obtain ⟨hj1, _⟩ := Finset.mem_filter.1 hj
      obtain ⟨_, hjj⟩ := Finset.mem_Icc.1 hj1
      exact grid_fine_term_le_nine hc0 hjstar (hjj.trans hjs) hm hk3 hjj
    · rw [nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast (Finset.card_filter_le _ _).trans hcard)
        (mul_nonneg (mul_nonneg h9 (sq_nonneg _)) (by positivity))
  calc _ ≤ k * (60 * (k : ℝ) ^ 2 * ((2 : ℝ) ^ k) ^ 5) + k * (9 * c * (k : ℝ) ^ 2 * ((2 : ℝ) ^ k) ^ 5) :=
        add_le_add h1 h2
    _ = (60 + 9 * c) * (k : ℝ) ^ 3 * ((2 : ℝ) ^ k) ^ 5 := by ring

/-- `D C k ^ 3 s ^ 5 exp (-(ε0 ^ 2 / (16 cs M ^ 2)) s / k ^ 4) → 0` as `k → ∞`, with
`s = 2 ^ k`, as in (5.36) of the differentiability preprint. The constant `D C` stands for
`(60 + 9 c_*) c_{A,R}` of the preprint, in general form. The proof follows `grid_stair_term_tendsto`
with the exponent `5` in place
of `4`, using `k ^ 3 s ^ 5 ≤ exp (8 k)` and `s ^ 5 / k ^ 5 → ∞`. -/
theorem grid_stair_term_tendsto_five {D C ε0 cs M : ℝ} (hε0 : 0 < ε0) (hcs : 0 < cs)
    (hM : 0 < M) :
    Tendsto (fun k : ℕ => D * C * (k : ℝ) ^ 3 * ((2 : ℝ) ^ k) ^ 5 *
      Real.exp (-(ε0 ^ 2 / (16 * cs * M ^ 2)) * ((2 : ℝ) ^ k / (k : ℝ) ^ 4))) atTop (𝓝 0) := by
  set a : ℝ := ε0 ^ 2 / (16 * cs * M ^ 2) with ha
  have ha0 : 0 < a := by positivity
  have h1 : Tendsto (fun k : ℕ => (k : ℝ) ^ 5 / 2 ^ k) atTop (𝓝 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt 5 (by norm_num)
  have h2 : ∀ᶠ k : ℕ in atTop, (k : ℝ) ^ 5 / 2 ^ k < a / 9 :=
    h1.eventually (gt_mem_nhds (by positivity))
  have hg : Tendsto (fun k : ℕ => Real.exp (-(k : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop
  have h3 : Tendsto (fun k : ℕ => (k : ℝ) ^ 3 * ((2 : ℝ) ^ k) ^ 5 *
      Real.exp (-a * ((2 : ℝ) ^ k / (k : ℝ) ^ 4))) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun k => by positivity) ?_ hg
    filter_upwards [h2, eventually_ge_atTop 1] with k hk hk1
    have kpos : (0 : ℝ) < k := by exact_mod_cast hk1
    have hA : 9 * (k : ℝ) ≤ a * ((2 : ℝ) ^ k / (k : ℝ) ^ 4) := by
      rw [← mul_div_assoc, le_div_iff₀ (by positivity)]
      have := (div_lt_iff₀ (by positivity)).1 hk
      nlinarith
    have hexp1 : Real.exp (-a * ((2 : ℝ) ^ k / (k : ℝ) ^ 4)) ≤ Real.exp (-(9 * (k : ℝ))) :=
      Real.exp_le_exp.2 (by linarith)
    have hk' : (k : ℝ) ≤ Real.exp k := by linarith [Real.add_one_le_exp (k : ℝ)]
    have e1 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
    have e2 : (2 : ℝ) ^ k ≤ Real.exp k :=
      calc (2 : ℝ) ^ k ≤ (Real.exp 1) ^ k := by gcongr
        _ = Real.exp k := by rw [← Real.exp_nat_mul]; simp
    have e3 : Real.exp (3 * (k : ℝ)) = Real.exp k ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    have e5 : Real.exp (5 * (k : ℝ)) = Real.exp k ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
    have hpoly : (k : ℝ) ^ 3 * ((2 : ℝ) ^ k) ^ 5 ≤ Real.exp (8 * (k : ℝ)) := by
      calc (k : ℝ) ^ 3 * ((2 : ℝ) ^ k) ^ 5 ≤ Real.exp k ^ 3 * Real.exp k ^ 5 := by gcongr
        _ = Real.exp (8 * (k : ℝ)) := by
          rw [← e3, ← e5, ← Real.exp_add]; ring_nf
    calc (k : ℝ) ^ 3 * ((2 : ℝ) ^ k) ^ 5 * Real.exp (-a * ((2 : ℝ) ^ k / (k : ℝ) ^ 4))
        ≤ Real.exp (8 * (k : ℝ)) * Real.exp (-(9 * (k : ℝ))) :=
          mul_le_mul hpoly hexp1 (Real.exp_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (-(k : ℝ)) := by rw [← Real.exp_add]; ring_nf
  have h4 := h3.const_mul (D * C)
  rw [mul_zero] at h4
  exact h4.congr (fun k => by ring)

/-- Eventual form of (5.36) of the differentiability preprint: for `C > 0`, `q0 > 0` and a
fixed `J`, the scalar
`D C k ^ 3 s ^ 5 exp (…)` is at most `C ∑_{j ≥ J} 2 ^ (5 j) e ^ (-q0 j ^ 2)` for all large `k`.
This is `grid_stair_term_eventually_le` with `76` replaced by `D` and `s ^ 4` by `s ^ 5`. -/
theorem grid_stair_term_eventually_le_five {C D q0 ε0 cs M : ℝ} (_hD : 0 ≤ D) (hC : 0 < C)
    (hq : 0 < q0) (hε0 : 0 < ε0) (hcs : 0 < cs) (hM : 0 < M) (J : ℕ) :
    ∃ k1 : ℕ, ∀ k : ℕ, k1 ≤ k → D * C * (k : ℝ) ^ 3 * ((2 : ℝ) ^ k) ^ 5 *
      Real.exp (-(ε0 ^ 2 / (16 * cs * M ^ 2)) * ((2 : ℝ) ^ k / (k : ℝ) ^ 4)) ≤
      C * ∑' i : ℕ, (2 : ℝ) ^ (5 * (i + J)) * Real.exp (-(q0 * ((i + J : ℕ) : ℝ) ^ 2)) := by
  have h := (grid_stair_term_tendsto_five (D := D) (C := C) hε0 hcs hM).eventually
    (gt_mem_nhds (grid_beta_pos hq hC J))
  obtain ⟨k1, hk1⟩ := eventually_atTop.1 h
  exact ⟨k1, fun k hk => (hk1 k hk).le⟩

end LPPDifferentiability
