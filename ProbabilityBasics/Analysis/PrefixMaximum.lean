/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic

/-!
# Sublinear growth of finite prefix maxima

If a real sequence divided by its index tends to zero, its inclusive finite
prefix maximum has the same sublinear growth. This elementary lemma extends
the shell estimate of JR1810.03580v3, Appendix B, Theorem B.3 to filled triangles.
-/

public section

open Filter
open scoped Topology

namespace ProbabilityBasics

/-- A real sequence whose terms are sublinear has an inclusive prefix maximum
that is sublinear as well. This elementary extension is used after the shell
estimate in JR1810.03580v3, Appendix B, Theorem B.3. -/
theorem tendsto_prefix_max_div_atTop_zero (a : ℕ → ℝ)
    (ha : Tendsto (fun n : ℕ => a n / (n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      (Finset.range (n + 1)).sup'
        ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ n)⟩ a / (n : ℝ))
      atTop (𝓝 0) := by
  let M : ℕ → ℝ := fun n =>
    (Finset.range (n + 1)).sup'
      ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ n)⟩ a
  change Tendsto (fun n : ℕ => M n / (n : ℝ)) atTop (𝓝 0)

  -- The initial value gives a lower bound for every nonempty prefix.
  have hzero_le (n : ℕ) : a 0 ≤ M n := by
    exact Finset.le_sup' a (Finset.mem_range.mpr (Nat.zero_lt_succ n))
  have ha0 : Tendsto (fun n : ℕ => a 0 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (a 0)

  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro c hc
    have hlow : ∀ᶠ n : ℕ in atTop, c < a 0 / (n : ℝ) :=
      ha0.eventually (Ioi_mem_nhds hc)
    filter_upwards [hlow] with n hn
    exact lt_of_lt_of_le hn
      (div_le_div_of_nonneg_right (hzero_le n) (Nat.cast_nonneg n))
  · intro ε hε
    let δ : ℝ := ε / 2
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hδε : δ < ε := by dsimp [δ]; linarith

    -- The hypothesis controls all indices after one fixed cutoff.
    have htail_event : ∀ᶠ k : ℕ in atTop, a k / (k : ℝ) < δ :=
      ha.eventually (Iio_mem_nhds hδ)
    obtain ⟨N, htail⟩ := eventually_atTop.1 htail_event
    let K : ℕ := max N 1
    have hNK : N ≤ K := le_max_left N 1
    have hKpos : 1 ≤ K := le_max_right N 1
    have hKlt : 0 < K := Nat.zero_lt_one.trans_le hKpos

    -- Keep the early, possibly signed values inside one fixed finite maximum.
    let C : ℝ := (Finset.range K).sup'
      ⟨0, Finset.mem_range.mpr hKlt⟩ a
    have hCdiv : Tendsto (fun n : ℕ => C / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat C
    have hCevent : ∀ᶠ n : ℕ in atTop, C / (n : ℝ) < δ :=
      hCdiv.eventually (Iio_mem_nhds hδ)
    obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 hCevent

    -- Beyond a large index, each term is bounded by the small linear scale.
    let Nbig : ℕ := max K (max N₁ 1)
    have hUpper : ∀ᶠ n : ℕ in atTop, M n / (n : ℝ) < ε := by
      refine eventually_atTop.2 ⟨Nbig, ?_⟩
      intro n hn
      have hKn : K ≤ n := (le_max_left K (max N₁ 1)).trans hn
      have hN₁n : N₁ ≤ n :=
        (le_max_left N₁ 1).trans ((le_max_right K (max N₁ 1)).trans hn)
      have h1n : 1 ≤ n :=
        (le_max_right N₁ 1).trans ((le_max_right K (max N₁ 1)).trans hn)
      have hnR : 0 < (n : ℝ) := by exact_mod_cast h1n
      have hCsmall : C < δ * (n : ℝ) :=
        (div_lt_iff₀ hnR).mp (hN₁ n hN₁n)

      have hterm (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
          a k ≤ δ * (n : ℝ) := by
        have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
        by_cases hkK : k < K
        · have hak : a k ≤ C :=
            Finset.le_sup' a (Finset.mem_range.mpr hkK)
          exact hak.trans hCsmall.le
        · have hKk : K ≤ k := Nat.le_of_not_gt hkK
          have hNk : N ≤ k := hNK.trans hKk
          have hkpos : 0 < k := Nat.zero_lt_one.trans_le (hKpos.trans hKk)
          have hkR : 0 < (k : ℝ) := by exact_mod_cast hkpos
          have hakRatio := htail k hNk
          have hak : a k < δ * (k : ℝ) := (div_lt_iff₀ hkR).mp hakRatio
          have hknR : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
          exact (le_of_lt hak).trans (mul_le_mul_of_nonneg_left hknR hδ.le)

      have hMsmall : M n ≤ δ * (n : ℝ) := by
        dsimp [M]
        exact Finset.sup'_le _ _ hterm
      have hratio : M n / (n : ℝ) ≤ δ := by
        calc
          M n / (n : ℝ) ≤ (δ * (n : ℝ)) / (n : ℝ) :=
            div_le_div_of_nonneg_right hMsmall hnR.le
          _ = δ := by rw [mul_div_cancel_right₀ _ hnR.ne']
      exact lt_of_le_of_lt hratio hδε

    exact hUpper

end ProbabilityBasics
