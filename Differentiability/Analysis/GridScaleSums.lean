/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Analysis.GridScaleCounts
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Grid scales: sums over scales, limits and the choice of `J`

Level-only arithmetic in the proof of the simultaneous grid connections and of the arbitrary
endpoints proposition (Proposition 5.9) of the differentiability preprint, using (5.32) to
(5.36) and (5.38) to (5.41) there. Here `s = 2 ^ k`, `w_j = 2 ^ (k - j)`,
`l_j = 2 ^ (m - 4 j - 1)`, and the constant `c` is `c_*` of the preprint.

## References

- C. Janjigian, F. Rassoul-Agha and T. Seppäläinen, *Differentiability of the shape function in
  the planar corner growth model*, preprint.
-/

public section

open Filter Topology

namespace LPPDifferentiability

/-- As in (5.34) of the differentiability preprint, the coarse term `60 j ^ 2 2 ^ (5 j) w_j ^ 2 ≤ 60
k ^ 2 s ^ 4`, given the
coarse condition `l_j ≥ 8 c j ^ 2 w_j` and `c j ^ 2 ≥ 1`. -/
theorem grid_coarse_term_le {m k j : ℕ} {c : ℝ} (hjk : j ≤ k) (hm : m ≤ 3 * k)
    (hc : 1 ≤ c * (j : ℝ) ^ 2)
    (hcoarse : 8 * (c * (j : ℝ) ^ 2 * 2 ^ (k - j)) ≤ (2 : ℝ) ^ (m - 4 * j - 1)) :
    60 * j ^ 2 * 2 ^ (5 * j) * (2 ^ (k - j)) ^ 2 ≤ 60 * k ^ 2 * (2 ^ k) ^ 4 := by
  have hw : (0 : ℝ) < 2 ^ (k - j) := by positivity
  have h1 : (2 : ℝ) ^ (k - j + 3) ≤ 2 ^ (m - 4 * j - 1) := by
    calc (2 : ℝ) ^ (k - j + 3) = 8 * 2 ^ (k - j) := by rw [pow_add]; ring
      _ ≤ 8 * (c * (j : ℝ) ^ 2 * 2 ^ (k - j)) := by nlinarith
      _ ≤ _ := hcoarse
  have h2 : k - j + 3 ≤ m - 4 * j - 1 := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 h1
  have h3 : 5 * j + 2 * (k - j) ≤ 4 * k := by omega
  calc 60 * j ^ 2 * 2 ^ (5 * j) * (2 ^ (k - j)) ^ 2 = 60 * j ^ 2 * 2 ^ (5 * j + 2 * (k - j)) := by
        rw [pow_add, ← pow_mul]; ring
    _ ≤ 60 * k ^ 2 * 2 ^ (4 * k) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 60 (Nat.pow_le_pow_left hjk 2))
          (Nat.pow_le_pow_right (by norm_num) h3)
    _ = 60 * k ^ 2 * (2 ^ k) ^ 4 := by rw [← pow_mul, mul_comm k 4]

/-- This auxiliary fine-term bound follows from `j ≤ k`; the source obtains `j ≤ k`
from its scale bounds (4.6), (5.1), and (5.5)-(5.6). Here `j ≤ k` is the input `hjk`. -/
theorem grid_fine_term_le {m k j jstar : ℕ} (hjstar : jstar = ⌈((m : ℝ) - 1) / 4⌉₊)
    (hjk : j ≤ k) (hm : m ≤ 3 * k) (hj : j ≤ jstar) :
    2 ^ (5 * j) * (2 ^ (k - j) + 1) ≤ 16 * (2 ^ k) ^ 4 := by
  have hb := (grid_jstar_bounds hjstar).2
  have hw : 1 ≤ 2 ^ (k - j) := Nat.one_le_two_pow
  calc 2 ^ (5 * j) * (2 ^ (k - j) + 1) ≤ 2 ^ (5 * j) * (2 * 2 ^ (k - j)) :=
        Nat.mul_le_mul_left _ (by omega)
    _ = 2 ^ (4 * j + k + 1) := by
        rw [show 4 * j + k + 1 = 5 * j + (k - j + 1) by omega, pow_add, pow_succ]; ring
    _ ≤ 2 ^ (4 * k + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 16 * (2 ^ k) ^ 4 := by rw [pow_add, ← pow_mul, mul_comm k 4]; ring

open scoped Classical in
/-- For the coarse/fine split in (5.32), combine the coarse estimate (5.34) with
`grid_fine_term_le` to obtain the stronger auxiliary bound `76 k ^ 3 s ^ 4`. The two
sums, over coarse scales (`l_j ≥ 8 c j ^ 2 w_j`) and fine scales (the others) with
`J ≤ j ≤ jstar`, add up to at most this bound. Hypotheses: `m ≤ 3 k`,
`k ≥ 4 k0 + 3`, `k0 > 0`, `J ≥ 1`, and `c ≥ 1`. -/
theorem grid_staircase_sum_le {m k k0 J jstar : ℕ} {c : ℝ}
    (hjstar : jstar = ⌈((m : ℝ) - 1) / 4⌉₊) (hm : m ≤ 3 * k) (hk : 4 * k0 + 3 ≤ k)
    (hk0 : 0 < k0) (hJ : 1 ≤ J) (hc : 1 ≤ c) :
    (∑ j ∈ (Finset.Icc J jstar).filter
        (fun j : ℕ => 8 * (c * (j : ℝ) ^ 2 * 2 ^ (k - j)) ≤ (2 : ℝ) ^ (m - 4 * j - 1)),
      60 * j ^ 2 * 2 ^ (5 * j) * (2 ^ (k - j)) ^ 2) +
    (∑ j ∈ (Finset.Icc J jstar).filter
        (fun j : ℕ => ¬ 8 * (c * (j : ℝ) ^ 2 * 2 ^ (k - j)) ≤ (2 : ℝ) ^ (m - 4 * j - 1)),
      2 ^ (5 * j) * (2 ^ (k - j) + 1)) ≤ 76 * k ^ 3 * (2 ^ k) ^ 4 := by
  have hjs : jstar ≤ k := (grid_scale_index_bounds hjstar hm hk hk0 le_rfl).1
  have hcard : (Finset.Icc J jstar).card ≤ k := by rw [Nat.card_Icc]; omega
  have h1 : (∑ j ∈ (Finset.Icc J jstar).filter
        (fun j : ℕ => 8 * (c * (j : ℝ) ^ 2 * 2 ^ (k - j)) ≤ (2 : ℝ) ^ (m - 4 * j - 1)),
      60 * j ^ 2 * 2 ^ (5 * j) * (2 ^ (k - j)) ^ 2) ≤ k * (60 * k ^ 2 * (2 ^ k) ^ 4) := by
    refine (Finset.sum_le_card_nsmul _ _ (60 * k ^ 2 * (2 ^ k) ^ 4) fun j hj => ?_).trans ?_
    · obtain ⟨hj1, hcl⟩ := Finset.mem_filter.1 hj
      obtain ⟨hJj, hjj⟩ := Finset.mem_Icc.1 hj1
      have hj1' : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hJ.trans hJj
      exact grid_coarse_term_le (hjj.trans hjs) hm (by nlinarith) hcl
    · rw [smul_eq_mul]
      exact Nat.mul_le_mul_right _ ((Finset.card_filter_le _ _).trans hcard)
  have h2 : (∑ j ∈ (Finset.Icc J jstar).filter
        (fun j : ℕ => ¬ 8 * (c * (j : ℝ) ^ 2 * 2 ^ (k - j)) ≤ (2 : ℝ) ^ (m - 4 * j - 1)),
      2 ^ (5 * j) * (2 ^ (k - j) + 1)) ≤ k * (16 * (2 ^ k) ^ 4) := by
    refine (Finset.sum_le_card_nsmul _ _ (16 * (2 ^ k) ^ 4) fun j hj => ?_).trans ?_
    · obtain ⟨hJj, hjj⟩ := Finset.mem_Icc.1 (Finset.mem_filter.1 hj).1
      exact grid_fine_term_le hjstar (hjj.trans hjs) hm hjj
    · rw [smul_eq_mul]
      exact Nat.mul_le_mul_right _ ((Finset.card_filter_le _ _).trans hcard)
  have hk3 : k ≤ k ^ 3 := Nat.le_self_pow (by norm_num) k
  calc _ ≤ k * (60 * k ^ 2 * (2 ^ k) ^ 4) + k * (16 * (2 ^ k) ^ 4) := Nat.add_le_add h1 h2
    _ ≤ k * (60 * k ^ 2 * (2 ^ k) ^ 4) + k ^ 3 * (16 * (2 ^ k) ^ 4) :=
        Nat.add_le_add_left (Nat.mul_le_mul_right _ hk3) _
    _ = 76 * k ^ 3 * (2 ^ k) ^ 4 := by ring

/-- As in (5.33) of the differentiability preprint: the series `∑ 2 ^ (5 j) e ^ (-q0 j ^ 2)`
converges. -/
theorem grid_beta_summable {q0 : ℝ} (hq : 0 < q0) :
    Summable (fun j : ℕ => (2 : ℝ) ^ (5 * j) * Real.exp (-(q0 * (j : ℝ) ^ 2))) := by
  refine Summable.of_norm_bounded_eventually (g := fun j : ℕ => ((1 : ℝ) / 2) ^ j)
    summable_geometric_two ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop ⌈6 / q0⌉₊] with j hj
  have hq6 : 6 ≤ q0 * j := by
    have : 6 / q0 ≤ j := le_trans (Nat.le_ceil _) (by exact_mod_cast hj)
    rwa [div_le_iff₀ hq, mul_comm] at this
  rw [Real.norm_of_nonneg (by positivity)]
  have e1 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
  have e6 : (2 : ℝ) ^ 6 ≤ Real.exp (q0 * j) :=
    calc (2 : ℝ) ^ 6 ≤ (Real.exp 1) ^ 6 := by gcongr
      _ = Real.exp 6 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ Real.exp (q0 * j) := Real.exp_le_exp.2 hq6
  have hE : (2 : ℝ) ^ (6 * j) ≤ Real.exp (q0 * (j : ℝ) ^ 2) :=
    calc (2 : ℝ) ^ (6 * j) = ((2 : ℝ) ^ 6) ^ j := by rw [pow_mul]
      _ ≤ (Real.exp (q0 * j)) ^ j := by gcongr
      _ = Real.exp (q0 * (j : ℝ) ^ 2) := by rw [← Real.exp_nat_mul]; ring_nf
  rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _), one_div, inv_pow, inv_mul_eq_div,
    le_div_iff₀ (by positivity), ← pow_add]
  rw [show 5 * j + j = 6 * j by ring]
  exact hE

/-- As in (5.33) of the differentiability preprint: the tail sums
`∑_{j ≥ J} 2 ^ (5 j) e ^ (-q0 j ^ 2)`, times any constant (`β_J = c_{A,R} ∑_{j ≥ J} …`),
tend to `0` as `J → ∞`. -/
theorem grid_beta_tendsto (q0 C : ℝ) :
    Tendsto (fun J : ℕ => C * ∑' i : ℕ,
      (2 : ℝ) ^ (5 * (i + J)) * Real.exp (-(q0 * ((i + J : ℕ) : ℝ) ^ 2))) atTop (𝓝 0) := by
  have h := (tendsto_sum_nat_add (fun j : ℕ =>
    (2 : ℝ) ^ (5 * j) * Real.exp (-(q0 * (j : ℝ) ^ 2)))).const_mul C
  rwa [mul_zero] at h

/-- `β_J > 0` for `C > 0` and `q0 > 0`. -/
theorem grid_beta_pos {q0 C : ℝ} (hq : 0 < q0) (hC : 0 < C) (J : ℕ) :
    0 < C * ∑' i : ℕ, (2 : ℝ) ^ (5 * (i + J)) * Real.exp (-(q0 * ((i + J : ℕ) : ℝ) ^ 2)) := by
  refine mul_pos hC ?_
  have hs := (summable_nat_add_iff J).2 (grid_beta_summable hq)
  exact hs.tsum_pos (fun i => by positivity) 0 (by positivity)

/-- As in (5.36) of the differentiability preprint, with (5.12):
`(ε0 s / k) ^ 2 / (16 c k ^ 2 s M ^ 2) = ε0 ^ 2 / (16 c M ^ 2) * (s / k ^ 4)`, that is,
`t_k = ε0 s / k` in the exponent. -/
theorem grid_badstair_exponent {ε0 cs M s : ℝ} {k : ℕ} (hk : 0 < k) (hs : 0 < s)
    (hcs : 0 < cs) (hM : 0 < M) :
    (ε0 * s / k) ^ 2 / (16 * cs * (k : ℝ) ^ 2 * s * M ^ 2) =
      ε0 ^ 2 / (16 * cs * M ^ 2) * (s / (k : ℝ) ^ 4) := by
  have hk' : (k : ℝ) ≠ 0 := by positivity
  field_simp

/-- `76 c k ^ 3 s ^ 4 exp (-(ε0 ^ 2 / (16 c_* M ^ 2)) s / k ^ 4) → 0` as `k → ∞`, with
`s = 2 ^ k`, as in (5.36) of the differentiability preprint. The constant `C` is the
preprint's `c_{A,R}`. -/
theorem grid_stair_term_tendsto {C ε0 cs M : ℝ} (hε0 : 0 < ε0) (hcs : 0 < cs) (hM : 0 < M) :
    Tendsto (fun k : ℕ => 76 * C * (k : ℝ) ^ 3 * ((2 : ℝ) ^ k) ^ 4 *
      Real.exp (-(ε0 ^ 2 / (16 * cs * M ^ 2)) * ((2 : ℝ) ^ k / (k : ℝ) ^ 4))) atTop (𝓝 0) := by
  set a : ℝ := ε0 ^ 2 / (16 * cs * M ^ 2) with ha
  have ha0 : 0 < a := by positivity
  have h1 : Tendsto (fun k : ℕ => (k : ℝ) ^ 5 / 2 ^ k) atTop (𝓝 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt 5 (by norm_num)
  have h2 : ∀ᶠ k : ℕ in atTop, (k : ℝ) ^ 5 / 2 ^ k < a / 8 :=
    h1.eventually (gt_mem_nhds (by positivity))
  have hg : Tendsto (fun k : ℕ => Real.exp (-(k : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop
  have h3 : Tendsto (fun k : ℕ => (k : ℝ) ^ 3 * ((2 : ℝ) ^ k) ^ 4 *
      Real.exp (-a * ((2 : ℝ) ^ k / (k : ℝ) ^ 4))) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun k => by positivity) ?_ hg
    filter_upwards [h2, eventually_ge_atTop 1] with k hk hk1
    have kpos : (0 : ℝ) < k := by exact_mod_cast hk1
    have hA : 8 * (k : ℝ) ≤ a * ((2 : ℝ) ^ k / (k : ℝ) ^ 4) := by
      rw [← mul_div_assoc, le_div_iff₀ (by positivity)]
      have := (div_lt_iff₀ (by positivity)).1 hk
      nlinarith
    have hexp1 : Real.exp (-a * ((2 : ℝ) ^ k / (k : ℝ) ^ 4)) ≤ Real.exp (-(8 * (k : ℝ))) :=
      Real.exp_le_exp.2 (by linarith)
    have hk' : (k : ℝ) ≤ Real.exp k := by linarith [Real.add_one_le_exp (k : ℝ)]
    have e1 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
    have e2 : (2 : ℝ) ^ k ≤ Real.exp k :=
      calc (2 : ℝ) ^ k ≤ (Real.exp 1) ^ k := by gcongr
        _ = Real.exp k := by rw [← Real.exp_nat_mul]; simp
    have e3 : Real.exp (3 * (k : ℝ)) = Real.exp k ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    have e4 : Real.exp (4 * (k : ℝ)) = Real.exp k ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    have hpoly : (k : ℝ) ^ 3 * ((2 : ℝ) ^ k) ^ 4 ≤ Real.exp (7 * (k : ℝ)) := by
      calc (k : ℝ) ^ 3 * ((2 : ℝ) ^ k) ^ 4 ≤ Real.exp k ^ 3 * Real.exp k ^ 4 := by gcongr
        _ = Real.exp (7 * (k : ℝ)) := by
          rw [← e3, ← e4, ← Real.exp_add]; ring_nf
    calc (k : ℝ) ^ 3 * ((2 : ℝ) ^ k) ^ 4 * Real.exp (-a * ((2 : ℝ) ^ k / (k : ℝ) ^ 4))
        ≤ Real.exp (7 * (k : ℝ)) * Real.exp (-(8 * (k : ℝ))) :=
          mul_le_mul hpoly hexp1 (Real.exp_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (-(k : ℝ)) := by rw [← Real.exp_add]; ring_nf
  have h4 := h3.const_mul (76 * C)
  rw [mul_zero] at h4
  exact h4.congr (fun k => by ring)

/-- As in (5.36) of the differentiability preprint: for `J` fixed, the scalar in (5.36) is at most
`β_J = C ∑_{j ≥ J} 2 ^ (5 j) e ^ (-q0 j ^ 2)` for all large `k` (the index `k1(J)`). -/
theorem grid_stair_term_eventually_le {C q0 ε0 cs M : ℝ} (hC : 0 < C) (hq : 0 < q0)
    (hε0 : 0 < ε0) (hcs : 0 < cs) (hM : 0 < M) (J : ℕ) :
    ∃ k1 : ℕ, ∀ k : ℕ, k1 ≤ k → 76 * C * (k : ℝ) ^ 3 * ((2 : ℝ) ^ k) ^ 4 *
      Real.exp (-(ε0 ^ 2 / (16 * cs * M ^ 2)) * ((2 : ℝ) ^ k / (k : ℝ) ^ 4)) ≤
      C * ∑' i : ℕ, (2 : ℝ) ^ (5 * (i + J)) * Real.exp (-(q0 * ((i + J : ℕ) : ℝ) ^ 2)) := by
  have h := (grid_stair_term_tendsto (C := C) hε0 hcs hM).eventually
    (gt_mem_nhds (grid_beta_pos hq hC J))
  obtain ⟨k1, hk1⟩ := eventually_atTop.1 h
  exact ⟨k1, fun k hk => (hk1 k hk).le⟩

private theorem summable_sq_div_two_pow :
    Summable (fun j : ℕ => (j : ℝ) ^ 2 / 2 ^ j) := by
  simpa [div_eq_mul_inv, inv_pow] using
    summable_pow_mul_geometric_of_norm_lt_one 2 (r := (2 : ℝ)⁻¹) (by norm_num)

/-- As in (5.38) of the differentiability preprint: for `c1 ≥ 0` and `ε > 0` there is `J0 ≥ 1` such
that every
`J ≥ J0` satisfies `16 c1 ∑_{j ≥ J} j ^ 2 2 ^ (-j) ≤ ε / 8`. -/
theorem grid_exists_J {c1 ε : ℝ} (hε : 0 < ε) :
    ∃ J0 : ℕ, 1 ≤ J0 ∧ ∀ J : ℕ, J0 ≤ J →
      16 * c1 * ∑' i : ℕ, ((i + J : ℕ) : ℝ) ^ 2 / 2 ^ (i + J) ≤ ε / 8 := by
  have h := (tendsto_sum_nat_add (fun j : ℕ => (j : ℝ) ^ 2 / 2 ^ j)).const_mul (16 * c1)
  rw [mul_zero] at h
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h.eventually (ge_mem_nhds (by positivity : (0 : ℝ) < ε / 8)))
  exact ⟨max N 1, le_max_right _ _, fun J hJ => hN J (le_trans (le_max_left _ _) hJ)⟩

/-- As in (5.41) of the differentiability preprint: with `n j ≤ 16` grid intervals at each scale `J
≤ j ≤ jstar ≤ k`,
`t_k = (ε / 512) s / k`, the total cost is at most `ε s / 8 + ε s / 16`, given the choice of `J`
((5.38) in the form `16 c1 ∑_{j ≥ J} j ^ 2 2 ^ (-j) ≤ ε / 8`). -/
theorem grid_extcost_le {c1 ε : ℝ} {k J jstar : ℕ} (n : ℕ → ℕ) (hc1 : 0 ≤ c1) (hε : 0 < ε)
    (hn : ∀ j, n j ≤ 16) (hJ1 : 1 ≤ J) (hjk : jstar ≤ k) (hk : 0 < k)
    (hJ : 16 * c1 * ∑' i : ℕ, ((i + J : ℕ) : ℝ) ^ 2 / 2 ^ (i + J) ≤ ε / 8) :
    ∑ j ∈ Finset.Icc J jstar, (n j : ℝ) *
        (c1 * (j : ℝ) ^ 2 * 2 ^ (k - j) + 2 * ((ε / 512) * 2 ^ k / k)) ≤
      ε * 2 ^ k / 8 + ε * 2 ^ k / 16 := by
  set s : ℝ := 2 ^ k with hs
  set t : ℝ := (ε / 512) * s / k with ht
  have hs0 : 0 < s := by positivity
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have ht0 : 0 ≤ t := by positivity
  have hsum : Summable (fun i : ℕ => ((i + J : ℕ) : ℝ) ^ 2 / 2 ^ (i + J)) :=
    (summable_nat_add_iff J).2 summable_sq_div_two_pow
  have hS : ∑ j ∈ Finset.Icc J jstar, (j : ℝ) ^ 2 / 2 ^ j ≤
      ∑' i : ℕ, ((i + J : ℕ) : ℝ) ^ 2 / 2 ^ (i + J) := by
    have : Finset.Icc J jstar = Finset.Ico J (jstar + 1) := by ext; simp
    rw [this, Finset.sum_Ico_eq_sum_range]
    calc _ = ∑ i ∈ Finset.range (jstar + 1 - J), ((i + J : ℕ) : ℝ) ^ 2 / 2 ^ (i + J) := by
          apply Finset.sum_congr rfl; intro i _; rw [add_comm J i]
      _ ≤ _ := hsum.sum_le_tsum _ (fun i _ => by positivity)
  have hterm : ∀ j ∈ Finset.Icc J jstar, (n j : ℝ) * (c1 * (j : ℝ) ^ 2 * 2 ^ (k - j) + 2 * t) ≤
      (16 * c1 * s) * ((j : ℝ) ^ 2 / 2 ^ j) + 32 * t := by
    intro j hj
    have hjk' : j ≤ k := (Finset.mem_Icc.1 hj).2.trans hjk
    have hw : (2 : ℝ) ^ (k - j) = s / 2 ^ j := by rw [hs, pow_sub₀ _ (by norm_num) hjk', div_eq_mul_inv]
    have hn' : (n j : ℝ) ≤ 16 := by exact_mod_cast hn j
    have hA : 0 ≤ c1 * (j : ℝ) ^ 2 * 2 ^ (k - j) + 2 * t := by positivity
    calc (n j : ℝ) * (c1 * (j : ℝ) ^ 2 * 2 ^ (k - j) + 2 * t)
        ≤ 16 * (c1 * (j : ℝ) ^ 2 * 2 ^ (k - j) + 2 * t) := mul_le_mul_of_nonneg_right hn' hA
      _ = (16 * c1 * s) * ((j : ℝ) ^ 2 / 2 ^ j) + 32 * t := by rw [hw]; ring
  have hcard : ((Finset.Icc J jstar).card : ℝ) ≤ k := by
    rw [Nat.card_Icc]; exact_mod_cast (by omega : jstar + 1 - J ≤ k)
  have hkt : (k : ℝ) * t = ε * s / 512 := by rw [ht]; field_simp
  calc _ ≤ ∑ j ∈ Finset.Icc J jstar, ((16 * c1 * s) * ((j : ℝ) ^ 2 / 2 ^ j) + 32 * t) :=
        Finset.sum_le_sum hterm
    _ = (16 * c1 * s) * ∑ j ∈ Finset.Icc J jstar, (j : ℝ) ^ 2 / 2 ^ j +
        ((Finset.Icc J jstar).card : ℝ) * (32 * t) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    _ ≤ s * (ε / 8) + (k : ℝ) * (32 * t) := by
        refine add_le_add ?_ (mul_le_mul_of_nonneg_right hcard (by positivity))
        calc (16 * c1 * s) * ∑ j ∈ Finset.Icc J jstar, (j : ℝ) ^ 2 / 2 ^ j
              ≤ (16 * c1 * s) * ∑' i : ℕ, ((i + J : ℕ) : ℝ) ^ 2 / 2 ^ (i + J) := by
                gcongr
            _ = s * (16 * c1 * ∑' i : ℕ, ((i + J : ℕ) : ℝ) ^ 2 / 2 ^ (i + J)) := by ring
            _ ≤ s * (ε / 8) := by gcongr
    _ = ε * s / 8 + ε * s / 16 := by
        have : (k : ℝ) * (32 * t) = 32 * ((k : ℝ) * t) := by ring
        rw [this, hkt]; ring

end LPPDifferentiability
