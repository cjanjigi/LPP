/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Analysis.Subadditive
import Mathlib.Tactic

/-! # Finite rates for positive-index subadditive sequences

The elementary Fekete step in Liggett (1985), (2.1).
The input at index zero is unconstrained and absent from the conclusion.
-/

public section

open Filter Set
open scoped Topology

namespace LPPDifferentiability

/-- Positive subadditivity and one common linear lower bound give a finite
rate, jointly characterized by convergence and the positive-index infimum. -/
theorem exists_positive_subadditive_rate (a : ℕ → ℝ)
    (hsub : ∀ m n : ℕ, 0 < m → 0 < n → a (m + n) ≤ a m + a n)
    (c : ℝ) (hlower : ∀ n : ℕ, 0 < n → c * (n : ℝ) ≤ a n) :
    ∃ γ : ℝ,
      Tendsto (fun n : ℕ => a (n + 1) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 γ) ∧
      γ = sInf (range (fun n : ℕ => a (n + 1) / ((n + 1 : ℕ) : ℝ))) := by
  let u : ℕ → ℝ := fun n => if n = 0 then 0 else a n
  have hu (n : ℕ) (hn : 0 < n) : u n = a n := ite_eq_right (Nat.ne_of_gt hn)
  have hzero : u 0 = 0 := ite_eq_left rfl
  have hs : Subadditive u := by
    intro m n
    by_cases hm : m = 0
    · simp only [hm, hzero, zero_add, le_refl]
    by_cases hn : n = 0
    · simp only [hn, hzero, add_zero, le_refl]
    rw [hu m (Nat.pos_of_ne_zero hm), hu n (Nat.pos_of_ne_zero hn),
      hu (m + n) (by omega)]
    exact hsub m n (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn)
  have hb : BddBelow (range (fun n : ℕ => u n / (n : ℝ))) := by
    refine ⟨min c 0, ?_⟩
    rintro x ⟨n, rfl⟩
    by_cases hn : n = 0
    · simp only [hn, Nat.cast_zero, div_zero]
      exact min_le_right _ _
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      exact (min_le_left c 0).trans ((le_div_iff₀ (Nat.cast_pos.mpr hnpos)).mpr
        (by simpa only [hu n hnpos] using hlower n hnpos))
  have himage : ((fun n : ℕ => u n / (n : ℝ)) '' Ici 1) =
      range (fun n : ℕ => a (n + 1) / ((n + 1 : ℕ) : ℝ)) := by
    ext x
    constructor
    · rintro ⟨n, hn, rfl⟩
      have hnpos : 0 < n := hn
      refine ⟨n - 1, ?_⟩
      have heq : n - 1 + 1 = n := by omega
      simp only [heq, hu n hnpos]
    · rintro ⟨n, rfl⟩
      exact ⟨n + 1, by simp, by simp only [hu (n + 1) (by omega)]⟩
  refine ⟨hs.lim, ?_, ?_⟩
  · have ht := (hs.tendsto_lim hb).comp (tendsto_add_atTop_nat 1)
    simpa only [Function.comp_def, hu _ (Nat.zero_lt_succ _)] using ht
  · rw [Subadditive.lim, himage]

end LPPDifferentiability
