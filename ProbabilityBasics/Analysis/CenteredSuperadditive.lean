/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Basic
import Mathlib.Tactic

/-!
# Finite bounds for centered proper-interval arrays

These are conditional finite-interval facts for an array defined only on
proper integer intervals. Nonnegativity and superadditivity of the array are
hypotheses; the module does not construct or identify the array `Q` defined
in Martin (2002), Section 3 (see (3.1)-(3.3)). The later stochastic and
joint-coupling steps are outside this module.
-/

public section

namespace LPPDifferentiability

/-- A positive natural block length gives a proper consecutive integer
interval. -/
theorem integer_block_interval_lt (a : ℤ) (j k : ℕ) (hk : 0 < k) :
    a + (j : ℤ) * (k : ℤ) < a + ((j : ℤ) + 1) * (k : ℤ) := by
  have hkZ : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hk
  calc
    a + (j : ℤ) * (k : ℤ) < (a + (j : ℤ) * (k : ℤ)) + (k : ℤ) :=
      lt_add_of_pos_right _ hkZ
    _ = a + ((j : ℤ) + 1) * (k : ℤ) := by ring

/-- Extending a proper interval on either side cannot decrease a
nonnegative superadditive array. The hypotheses and every array evaluation
refer only to proper intervals. -/
theorem proper_interval_mono_of_nonneg_superadditive
    (Q : ∀ a b : ℤ, a < b → ℝ)
    (hQ_nonneg : ∀ a b (hab : a < b), 0 ≤ Q a b hab)
    (hQ_superadd : ∀ a b c (hab : a < b) (hbc : b < c),
      Q a b hab + Q b c hbc ≤ Q a c (lt_trans hab hbc))
    {a b c d : ℤ} (hab : a ≤ b) (hbc : b < c) (hcd : c ≤ d)
    (had : a < d) :
    Q b c hbc ≤ Q a d had := by
  by_cases habEq : a = b
  · subst b
    by_cases hcdEq : c = d
    · subst d
      exact le_rfl
    · have hcd' : c < d := lt_of_le_of_ne hcd hcdEq
      calc
        Q a c hbc ≤ Q a c hbc + Q c d hcd' :=
          le_add_of_nonneg_right (hQ_nonneg c d hcd')
        _ ≤ Q a d (lt_trans hbc hcd') := hQ_superadd a c d hbc hcd'
        _ = Q a d had := rfl
  · have hab' : a < b := lt_of_le_of_ne hab habEq
    by_cases hcdEq : c = d
    · subst d
      calc
        Q b c hbc ≤ Q a b hab' + Q b c hbc :=
          le_add_of_nonneg_left (hQ_nonneg a b hab')
        _ ≤ Q a c (lt_trans hab' hbc) := hQ_superadd a b c hab' hbc
        _ = Q a c had := rfl
    · have hcd' : c < d := lt_of_le_of_ne hcd hcdEq
      calc
        Q b c hbc ≤ Q a b hab' + Q b c hbc :=
          le_add_of_nonneg_left (hQ_nonneg a b hab')
        _ ≤ Q a c (lt_trans hab' hbc) := hQ_superadd a b c hab' hbc
        _ ≤ Q a c (lt_trans hab' hbc) + Q c d hcd' :=
          le_add_of_nonneg_right (hQ_nonneg c d hcd')
        _ ≤ Q a d (lt_trans (lt_trans hab' hbc) hcd') :=
          hQ_superadd a c d (lt_trans hab' hbc) hcd'
        _ = Q a d had := rfl

/-- The sum over `n` adjacent blocks is bounded by the value on their full
interval. This is the finite induction step for any proper-interval array
that is superadditive; no stationarity or limit assumption is used. -/
theorem proper_interval_block_sum_le
    (Q : ∀ a b : ℤ, a < b → ℝ)
    (hQ_superadd : ∀ a b c (hab : a < b) (hbc : b < c),
      Q a b hab + Q b c hbc ≤ Q a c (lt_trans hab hbc))
    (a : ℤ) (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    (∑ j ∈ Finset.range n,
      Q (a + (j : ℤ) * (k : ℤ))
        (a + ((j : ℤ) + 1) * (k : ℤ))
        (integer_block_interval_lt a j k hk)) ≤
      Q a (a + (n : ℤ) * (k : ℤ)) (by
        have hnZ : (0 : ℤ) < (n : ℤ) := by exact_mod_cast hn
        have hkZ : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hk
        exact lt_add_of_pos_right a (mul_pos hnZ hkZ)) := by
  induction n with
  | zero => omega
  | succ n ih =>
      rw [Finset.sum_range_succ]
      by_cases hn0 : n = 0
      · subst n
        simp only [Finset.range_zero, Finset.sum_empty, add_zero, Nat.cast_zero,
          zero_mul, Nat.cast_one, zero_add, one_mul]
        exact le_rfl
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
        have hnZ : (0 : ℤ) < (n : ℤ) := by exact_mod_cast hnpos
        have hkZ : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hk
        have hwhole : a < a + (n : ℤ) * (k : ℤ) :=
          lt_add_of_pos_right a (mul_pos hnZ hkZ)
        have hlast := integer_block_interval_lt a n k hk
        calc
          (∑ j ∈ Finset.range n,
              Q (a + (j : ℤ) * (k : ℤ))
                (a + ((j : ℤ) + 1) * (k : ℤ))
                (integer_block_interval_lt a j k hk)) +
              Q (a + (n : ℤ) * (k : ℤ))
                (a + ((n : ℤ) + 1) * (k : ℤ)) hlast ≤
              Q a (a + (n : ℤ) * (k : ℤ)) hwhole +
                Q (a + (n : ℤ) * (k : ℤ))
                  (a + ((n : ℤ) + 1) * (k : ℤ)) hlast :=
            add_le_add (ih hnpos) le_rfl
          _ ≤ Q a (a + ((Nat.succ n : ℕ) : ℤ) * (k : ℤ)) (by
              have hendpoint :
                  a + ((Nat.succ n : ℕ) : ℤ) * (k : ℤ) =
                    a + ((n : ℤ) + 1) * (k : ℤ) := by simp
              rw [hendpoint]
              exact lt_trans hwhole hlast) := by
                simpa only [Nat.cast_succ, add_mul, one_mul, add_assoc] using
                  hQ_superadd a (a + (n : ℤ) * (k : ℤ))
                    (a + ((n : ℤ) + 1) * (k : ℤ)) hwhole hlast

/-- The `2m` consecutive blocks from `-mk` to `mk` have total value at most
the value on that full interval. In the displayed sum, each interval is
`[(-m + j)k, (-m + j + 1)k]`; all are proper because `k > 0`. -/
theorem centered_interval_block_sum_le
    (Q : ∀ a b : ℤ, a < b → ℝ)
    (hQ_superadd : ∀ a b c (hab : a < b) (hbc : b < c),
      Q a b hab + Q b c hbc ≤ Q a c (lt_trans hab hbc))
    (m k : ℕ) (hm : 0 < m) (hk : 0 < k) :
    (∑ j ∈ Finset.range (2 * m),
      Q ((-(m : ℤ) + (j : ℤ)) * (k : ℤ))
        ((-(m : ℤ) + (j : ℤ) + 1) * (k : ℤ)) (by
          have hkZ : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hk
          have hstart :
              ((-(m : ℤ) + (j : ℤ)) * (k : ℤ)) + (k : ℤ) =
                (-(m : ℤ) + (j : ℤ) + 1) * (k : ℤ) := by ring
          rw [← hstart]
          exact lt_add_of_pos_right _ hkZ)) ≤
      Q (-(m : ℤ) * (k : ℤ)) ((m : ℤ) * (k : ℤ)) (by
        have hmZ : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
        have hkZ : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hk
        have hmk : (0 : ℤ) < (m : ℤ) * (k : ℤ) := mul_pos hmZ hkZ
        have hneg : -((m : ℤ) * (k : ℤ)) < (m : ℤ) * (k : ℤ) := by
          linarith
        simpa only [neg_mul] using hneg) := by
  have hblocks := proper_interval_block_sum_le Q hQ_superadd
    (-(m : ℤ) * (k : ℤ)) (2 * m) k (by omega) hk
  have hsum :
      (∑ j ∈ Finset.range (2 * m),
        Q ((-(m : ℤ) + (j : ℤ)) * (k : ℤ))
          ((-(m : ℤ) + (j : ℤ) + 1) * (k : ℤ)) (by
            have hkZ : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hk
            have hstart :
                ((-(m : ℤ) + (j : ℤ)) * (k : ℤ)) + (k : ℤ) =
                  (-(m : ℤ) + (j : ℤ) + 1) * (k : ℤ) := by ring
            rw [← hstart]
            exact lt_add_of_pos_right _ hkZ)) =
      (∑ j ∈ Finset.range (2 * m),
        Q (-(m : ℤ) * (k : ℤ) + (j : ℤ) * (k : ℤ))
          (-(m : ℤ) * (k : ℤ) + ((j : ℤ) + 1) * (k : ℤ))
          (integer_block_interval_lt (-(m : ℤ) * (k : ℤ)) j k hk)) := by
    apply Finset.sum_congr rfl
    intro j _
    have hleft :
        (-(m : ℤ) + (j : ℤ)) * (k : ℤ) =
          -(m : ℤ) * (k : ℤ) + (j : ℤ) * (k : ℤ) := by ring
    have hright :
        (-(m : ℤ) + (j : ℤ) + 1) * (k : ℤ) =
          -(m : ℤ) * (k : ℤ) + ((j : ℤ) + 1) * (k : ℤ) := by ring
    simp only [hleft, hright]
  have hfull :
      -(m : ℤ) * (k : ℤ) + ((2 * m : ℕ) : ℤ) * (k : ℤ) =
        (m : ℤ) * (k : ℤ) := by
    rw [Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [hsum]
  simpa only [hfull] using hblocks

/-- With the natural quotient `m = n / k`, the centered block sum is bounded
by the value on `[-n,n]`. This uses only `k ≤ n`, `k > 0`, nonnegativity,
and superadditivity; it does not assert a joint coupling or a limit result. -/
theorem centered_interval_floor_block_sum_le
    (Q : ∀ a b : ℤ, a < b → ℝ)
    (hQ_nonneg : ∀ a b (hab : a < b), 0 ≤ Q a b hab)
    (hQ_superadd : ∀ a b c (hab : a < b) (hbc : b < c),
      Q a b hab + Q b c hbc ≤ Q a c (lt_trans hab hbc))
    (n k : ℕ) (hnk : k ≤ n) (hk : 0 < k) :
    (∑ j ∈ Finset.range (2 * (n / k)),
      Q ((-((n / k : ℕ) : ℤ) + (j : ℤ)) * (k : ℤ))
        ((-((n / k : ℕ) : ℤ) + (j : ℤ) + 1) * (k : ℤ)) (by
          have hkZ : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hk
          have hstart :
              ((-((n / k : ℕ) : ℤ) + (j : ℤ)) * (k : ℤ)) + (k : ℤ) =
                (-((n / k : ℕ) : ℤ) + (j : ℤ) + 1) * (k : ℤ) := by ring
          rw [← hstart]
          exact lt_add_of_pos_right _ hkZ)) ≤
      Q (-(n : ℤ)) (n : ℤ) (by omega) := by
  have hquot : 0 < n / k := by
    have hquot1 : 1 ≤ n / k :=
      (Nat.le_div_iff_mul_le hk).2 (by simpa only [one_mul] using hnk)
    exact lt_of_lt_of_le Nat.zero_lt_one hquot1
  have hdiv := Nat.div_mul_le_self n k
  have hcenter := centered_interval_block_sum_le Q hQ_superadd (n / k) k hquot hk
  have hmk_le : ((n / k : ℕ) : ℤ) * (k : ℤ) ≤ (n : ℤ) := by
    exact_mod_cast hdiv
  have hmZ : (0 : ℤ) < ((n / k : ℕ) : ℤ) := by exact_mod_cast hquot
  have hkZ : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hk
  have hmk_pos : (0 : ℤ) < ((n / k : ℕ) : ℤ) * (k : ℤ) :=
    mul_pos hmZ hkZ
  have hleft0 :
      -(n : ℤ) ≤ -(((n / k : ℕ) : ℤ) * (k : ℤ)) := by omega
  have hleft :
      -(n : ℤ) ≤ -((n / k : ℕ) : ℤ) * (k : ℤ) := by
    simpa only [neg_mul] using hleft0
  have hmid0 :
      -(((n / k : ℕ) : ℤ) * (k : ℤ)) <
        ((n / k : ℕ) : ℤ) * (k : ℤ) := by linarith
  have hmid :
      -((n / k : ℕ) : ℤ) * (k : ℤ) <
        ((n / k : ℕ) : ℤ) * (k : ℤ) := by
    simpa only [neg_mul] using hmid0
  have had : -(n : ℤ) < (n : ℤ) := by omega
  have hmono := proper_interval_mono_of_nonneg_superadditive Q hQ_nonneg
    hQ_superadd hleft hmid hmk_le had
  calc
    (∑ j ∈ Finset.range (2 * (n / k)),
      Q ((-((n / k : ℕ) : ℤ) + (j : ℤ)) * (k : ℤ))
        ((-((n / k : ℕ) : ℤ) + (j : ℤ) + 1) * (k : ℤ)) (by
          have hkZ : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hk
          have hstart :
              ((-((n / k : ℕ) : ℤ) + (j : ℤ)) * (k : ℤ)) + (k : ℤ) =
                (-((n / k : ℕ) : ℤ) + (j : ℤ) + 1) * (k : ℤ) := by ring
          rw [← hstart]
          exact lt_add_of_pos_right _ hkZ)) ≤
        Q (-((n / k : ℕ) : ℤ) * (k : ℤ))
          (((n / k : ℕ) : ℤ) * (k : ℤ)) (by omega) := hcenter
    _ ≤ Q (-(n : ℤ)) (n : ℤ) (by omega) := hmono

end LPPDifferentiability
