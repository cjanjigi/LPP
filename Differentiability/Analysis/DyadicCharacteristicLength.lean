/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Order.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# First dyadic characteristic length

The arithmetic part of the proposition on characteristic lengths. For an
arbitrary family `P : ℕ → ℕ → ℝ`, where `P k n` stands for the crossing
probability at scale `2 ^ k` and length `n`, and for `q0 < 1`, the first
dyadic `L = 2 ^ m` whose window `(L / 2, L]` contains an integer `n` with
`P k n ≤ q0` exists, is at most `2 ^ (3 * k)`, grows faster than `2 ^ k`, and
every integer `1 ≤ n < L / 2` has `P k n > q0`.

The two inputs are the short-length statement (the infimum over
`1 ≤ n ≤ C * 2 ^ k` tends to `1`) and the bound at length `2 ^ (3 * k)`.
-/

public section

namespace LPPDifferentiability

open Filter

/-- Every integer `n ≥ 1` lies in the window `(2 ^ j / 2, 2 ^ j]` of some dyadic.
The smallest dyadic `1` has window `(1/2, 1]`, whose only integer is `1`. -/
private theorem exists_dyadic_window (n : ℕ) (hn : 1 ≤ n) :
    ∃ j : ℕ, (2 : ℝ) ^ j / 2 < n ∧ (n : ℝ) ≤ 2 ^ j := by
  refine ⟨Nat.clog 2 n, ?_, ?_⟩
  · rcases Nat.eq_or_lt_of_le hn with h | h
    · subst h
      norm_num
    · have h1 : 2 ^ (Nat.clog 2 n).pred < n := Nat.pow_pred_clog_lt_self (by norm_num) h
      have hpos : 0 < Nat.clog 2 n := Nat.clog_pos (by norm_num) h
      have h2 : (2 : ℝ) ^ (Nat.clog 2 n).pred < n := by exact_mod_cast h1
      have h3 : (2 : ℝ) ^ Nat.clog 2 n = 2 * 2 ^ (Nat.clog 2 n).pred := by
        rw [← pow_succ']
        exact congrArg _ (Nat.succ_pred_eq_of_pos hpos).symm
      rw [h3]
      linarith
  · exact_mod_cast Nat.le_pow_clog (by norm_num) n

/-- At a fixed scale index `k`, the first dyadic exists once the window at
`2 ^ (3 * k)` contains a good length, and it is at most `3 * k`. -/
private theorem first_dyadic_exists (P : ℕ → ℕ → ℝ) (q0 : ℝ) (k : ℕ)
    (h : P k (2 ^ (3 * k)) ≤ q0) :
    ∃ m : ℕ, (∃ n : ℕ, (2 : ℝ) ^ m / 2 < n ∧ (n : ℝ) ≤ 2 ^ m ∧ P k n ≤ q0) ∧
      (∀ j : ℕ, (∃ n : ℕ, (2 : ℝ) ^ j / 2 < n ∧ (n : ℝ) ≤ 2 ^ j ∧ P k n ≤ q0) → m ≤ j) ∧
      m ≤ 3 * k := by
  classical
  have hex : ∃ j : ℕ, ∃ n : ℕ, (2 : ℝ) ^ j / 2 < n ∧ (n : ℝ) ≤ 2 ^ j ∧ P k n ≤ q0 := by
    refine ⟨3 * k, 2 ^ (3 * k), ?_, ?_, h⟩
    · push_cast
      have : (0 : ℝ) < 2 ^ (3 * k) := by positivity
      linarith
    · push_cast
      exact le_refl _
  refine ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min' hex hj, ?_⟩
  refine Nat.find_min' hex ⟨2 ^ (3 * k), ?_, ?_, h⟩
  · push_cast
    have : (0 : ℝ) < 2 ^ (3 * k) := by positivity
    linarith
  · push_cast
    exact le_refl _

/-- The characteristic lengths. For arbitrary `P` and `q0 < 1`, if eventually
`P k (2 ^ (3 * k)) ≤ q0` and, for every `C > 0` and `c < 1`, eventually every
integer `1 ≤ n ≤ C * 2 ^ k` has `c < P k n`, then there is a positive `k0` and
functions `m` and `nk` so that for `k ≥ k0` the dyadic `L = 2 ^ m k` is the first
one whose window `(L / 2, L]` contains an integer `n` with `P k n ≤ q0`,
`L ≤ 2 ^ (3 * k)`, every integer `1 ≤ n < L / 2` has `q0 < P k n`, and `nk k`
is a minimizer of `P k` over the window with `P k (nk k) ≤ q0`. Moreover
`L / 2 ^ k` tends to infinity. -/
theorem exists_first_dyadic_characteristic_length (P : ℕ → ℕ → ℝ) (q0 : ℝ) (hq0 : q0 < 1)
    (htilt : ∀ᶠ k : ℕ in atTop, P k (2 ^ (3 * k)) ≤ q0)
    (hshort : ∀ C : ℝ, 0 < C → ∀ c : ℝ, c < 1 →
      ∀ᶠ k : ℕ in atTop, ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ C * 2 ^ k → c < P k n) :
    ∃ k0 : ℕ, 0 < k0 ∧ ∃ m nk : ℕ → ℕ,
      Tendsto (fun k : ℕ => (2 : ℝ) ^ m k / 2 ^ k) atTop atTop ∧
      ∀ k : ℕ, k0 ≤ k →
        (∃ n : ℕ, (2 : ℝ) ^ m k / 2 < n ∧ (n : ℝ) ≤ 2 ^ m k ∧ P k n ≤ q0) ∧
        (∀ j : ℕ, (∃ n : ℕ, (2 : ℝ) ^ j / 2 < n ∧ (n : ℝ) ≤ 2 ^ j ∧ P k n ≤ q0) →
          m k ≤ j) ∧
        m k ≤ 3 * k ∧
        (∀ n : ℕ, 1 ≤ n → (n : ℝ) < 2 ^ m k / 2 → q0 < P k n) ∧
        ((2 : ℝ) ^ m k / 2 < nk k ∧ (nk k : ℝ) ≤ 2 ^ m k ∧ P k (nk k) ≤ q0 ∧
          ∀ n : ℕ, (2 : ℝ) ^ m k / 2 < n → (n : ℝ) ≤ 2 ^ m k → P k (nk k) ≤ P k n) := by
  classical
  obtain ⟨k1, hk1⟩ := eventually_atTop.1 htilt
  refine ⟨max k1 1, lt_max_of_lt_right Nat.one_pos, ?_⟩
  have key : ∀ k : ℕ, ∃ m nk : ℕ, max k1 1 ≤ k →
      (∃ n : ℕ, (2 : ℝ) ^ m / 2 < n ∧ (n : ℝ) ≤ 2 ^ m ∧ P k n ≤ q0) ∧
      (∀ j : ℕ, (∃ n : ℕ, (2 : ℝ) ^ j / 2 < n ∧ (n : ℝ) ≤ 2 ^ j ∧ P k n ≤ q0) → m ≤ j) ∧
      m ≤ 3 * k ∧
      (∀ n : ℕ, 1 ≤ n → (n : ℝ) < 2 ^ m / 2 → q0 < P k n) ∧
      ((2 : ℝ) ^ m / 2 < nk ∧ (nk : ℝ) ≤ 2 ^ m ∧ P k nk ≤ q0 ∧
        ∀ n : ℕ, (2 : ℝ) ^ m / 2 < n → (n : ℝ) ≤ 2 ^ m → P k nk ≤ P k n) := by
    intro k
    by_cases hk : max k1 1 ≤ k
    · obtain ⟨m, ⟨n0, hn0lo, hn0hi, hn0P⟩, hmin, hm3⟩ :=
        first_dyadic_exists P q0 k (hk1 k (le_trans (le_max_left _ _) hk))
      have hn0pos : 1 ≤ n0 := by
        have : (0 : ℝ) < n0 := lt_trans (by positivity) hn0lo
        exact_mod_cast this
      have hne : ((Finset.Icc 1 (2 ^ m)).filter
          (fun n : ℕ => (2 : ℝ) ^ m / 2 < n)).Nonempty := by
        refine ⟨n0, Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hn0pos, ?_⟩, hn0lo⟩⟩
        exact_mod_cast hn0hi
      obtain ⟨nk, hnk, hnkmin⟩ := Finset.exists_min_image _ (P k) hne
      obtain ⟨hnkIcc, hnklo⟩ := Finset.mem_filter.1 hnk
      have hnkhi : (nk : ℝ) ≤ 2 ^ m := by exact_mod_cast (Finset.mem_Icc.1 hnkIcc).2
      have hnkmin' : ∀ n : ℕ, (2 : ℝ) ^ m / 2 < n → (n : ℝ) ≤ 2 ^ m → P k nk ≤ P k n := by
        intro n hlo hhi
        have hnpos : 1 ≤ n := by
          have : (0 : ℝ) < n := lt_trans (by positivity) hlo
          exact_mod_cast this
        refine hnkmin n (Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hnpos, ?_⟩, hlo⟩)
        exact_mod_cast hhi
      refine ⟨m, nk, fun _ => ⟨⟨n0, hn0lo, hn0hi, hn0P⟩, hmin, hm3, ?_,
        hnklo, hnkhi, le_trans (hnkmin' n0 hn0lo hn0hi) hn0P, hnkmin'⟩⟩
      intro n hn hnlt
      by_contra hcon
      obtain ⟨j, hjlo, hjhi⟩ := exists_dyadic_window n hn
      have hle : m ≤ j := hmin j ⟨n, hjlo, hjhi, not_lt.1 hcon⟩
      have h2 : (2 : ℝ) ^ j ≤ 2 ^ (m - 1) * 2 ^ (j - m + 1) := by
        rw [← pow_add]
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      have hjm : (2 : ℝ) ^ m ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hle
      linarith
    · exact ⟨0, 0, fun h => absurd h hk⟩
  choose m nk hmnk using key
  refine ⟨m, nk, ?_, fun k hk => hmnk k hk⟩
  refine tendsto_atTop.2 fun b => ?_
  have hC : (0 : ℝ) < max b 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  filter_upwards [hshort (max b 1) hC q0 hq0, eventually_ge_atTop (max k1 1)] with k hk hkk0
  obtain ⟨_, _, _, _, hnklo, hnkhi, hnkP, -⟩ := hmnk k hkk0
  have hnkpos : 1 ≤ nk k := by
    have : (0 : ℝ) < nk k := lt_trans (by positivity) hnklo
    exact_mod_cast this
  have hnot : ¬ ((nk k : ℝ) ≤ max b 1 * 2 ^ k) := fun hle =>
    absurd (hk (nk k) hnkpos hle) (not_lt.2 hnkP)
  have hlt : max b 1 * 2 ^ k < 2 ^ m k := lt_of_lt_of_le (not_le.1 hnot) hnkhi
  rw [le_div_iff₀ (by positivity)]
  exact le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) hlt.le

end LPPDifferentiability
