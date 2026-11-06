/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.MeasureTheory.Measure.Basic

/-! # Finite block inequalities from origin subadditivity

The finite block argument in Liggett (1985), equations (2.5) and (2.8), from
the origin-only almost-everywhere subadditivity condition (1.7). -/

public section

open MeasureTheory

namespace LPPDifferentiability

private theorem ae_liggett_block_bound_aux {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (A : ℕ → ℕ → Ω → ℝ)
    (hsub : ∀ m n : ℕ, 0 < m → m < n →
      ∀ᵐ ω ∂μ, A 0 n ω ≤ A 0 m ω + A m n ω)
    (k : ℕ) (hk : 0 < k) :
    ∀ q : ℕ, 0 < q → ∀ᵐ ω ∂μ,
      A 0 (q * k) ω ≤ ∑ i ∈ Finset.range q, A (i * k) ((i + 1) * k) ω := by
  intro q
  induction q with
  | zero =>
      intro hq
      exact False.elim (Nat.lt_irrefl 0 hq)
  | succ q ih =>
      intro hq
      by_cases hq0 : q = 0
      · subst q
        exact ae_of_all μ (fun ω => by simp)
      · have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
        have hcut_pos : 0 < q * k := Nat.mul_pos hqpos hk
        have hcut_lt : q * k < (q + 1) * k := by
          rw [Nat.add_mul, Nat.one_mul]
          exact Nat.lt_add_of_pos_right hk
        have hstep := hsub (q * k) ((q + 1) * k) hcut_pos hcut_lt
        filter_upwards [ih hqpos, hstep] with ω hprev hstep
        calc
          A 0 ((q + 1) * k) ω ≤ A 0 (q * k) ω + A (q * k) ((q + 1) * k) ω := hstep
          _ ≤ (∑ i ∈ Finset.range q, A (i * k) ((i + 1) * k) ω) +
              A (q * k) ((q + 1) * k) ω := add_le_add hprev le_rfl
          _ = ∑ i ∈ Finset.range (q + 1), A (i * k) ((i + 1) * k) ω := by
              rw [Finset.sum_range_succ]

/-- Repeated strict-interior splits of the origin give the whole-block bound
from Liggett (1985), equation (2.5). The input uses only the subadditivity condition (1.7)
of Liggett (1985). -/
theorem liggett_origin_block_bound_ae {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (A : ℕ → ℕ → Ω → ℝ)
    (hsub : ∀ m n : ℕ, 0 < m → m < n →
      ∀ᵐ ω ∂μ, A 0 n ω ≤ A 0 m ω + A m n ω)
    (k q : ℕ) (hk : 0 < k) (hq : 0 < q) :
    ∀ᵐ ω ∂μ,
      A 0 (q * k) ω ≤ ∑ i ∈ Finset.range q, A (i * k) ((i + 1) * k) ω :=
  ae_liggett_block_bound_aux A hsub k hk q hq

/-- One further strict-interior split gives the positive remainder estimate
in Liggett (1985), equation (2.8). -/
theorem liggett_origin_block_remainder_ae {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (A : ℕ → ℕ → Ω → ℝ)
    (hsub : ∀ m n : ℕ, 0 < m → m < n →
      ∀ᵐ ω ∂μ, A 0 n ω ≤ A 0 m ω + A m n ω)
    (k q j : ℕ) (hk : 0 < k) (hq : 0 < q) (hj : 0 < j) :
    ∀ᵐ ω ∂μ,
      A 0 (q * k + j) ω ≤
        (∑ i ∈ Finset.range q, A (i * k) ((i + 1) * k) ω) +
          A (q * k) (q * k + j) ω := by
  have hblock := liggett_origin_block_bound_ae A hsub k q hk hq
  have hcut_pos : 0 < q * k := Nat.mul_pos hq hk
  have hcut_lt : q * k < q * k + j := Nat.lt_add_of_pos_right hj
  have hstep := hsub (q * k) (q * k + j) hcut_pos hcut_lt
  filter_upwards [hblock, hstep] with ω hblock hstep
  calc
    A 0 (q * k + j) ω ≤ A 0 (q * k) ω + A (q * k) (q * k + j) ω := hstep
    _ ≤ (∑ i ∈ Finset.range q, A (i * k) ((i + 1) * k) ω) +
        A (q * k) (q * k + j) ω := add_le_add hblock le_rfl

end LPPDifferentiability
