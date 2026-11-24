/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.FlatTop.HalfLineConvergence
import Differentiability.Probability.HalfLineEdgeDeviation
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Tactic.Linarith

/-! A finite limiting half-line speed is the constant infimum of the expected rates. -/

public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace LPPDifferentiability.FinalDraft

/-- For any slope above the infimum of the expected rates, the half-line
edge eventually lies below the corresponding line almost surely. -/
private theorem ae_eventually_halfLineEdge_lt_of_isGLB (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hν : 0 < ν {1}) {β c : ℝ} (hβc : β < c)
    (hβ : IsGLB (Set.range fun n : ℕ =>
      (∫ ω, (halfLineEdge ω (n + 1) : ℝ) ∂environmentLaw ν) / ((n : ℝ) + 1)) β) :
    ∀ᵐ ω ∂environmentLaw ν, ∀ᶠ n : ℕ in atTop, (halfLineEdge ω n : ℝ) < c * n := by
  obtain ⟨r, ⟨k, rfl⟩, hk⟩ : ∃ r ∈ Set.range (fun n : ℕ =>
      (∫ ω, (halfLineEdge ω (n + 1) : ℝ) ∂environmentLaw ν) / ((n : ℝ) + 1)), r < c := by
    by_contra! h
    exact hβc.not_ge (hβ.2 h)
  have hmean : (∫ ω, (halfLineEdge ω (k + 1) : ℝ) ∂environmentLaw ν) <
      c * ((k + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_add, Nat.cast_one]
    exact (div_lt_iff₀ (by positivity : 0 < ((k : ℝ) + 1))).mp hk
  obtain ⟨A, B, hA, hB, htail⟩ :=
    halfLineEdge_upper_deviation ν hν c (k + 1) (Nat.succ_pos _) hmean
  let E (n : ℕ) : Set Environment := {ω | c * n ≤ (halfLineEdge ω n : ℝ)}
  let q : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-B))
  have hq : q < 1 := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hB))
  have hEn (n : ℕ) : environmentLaw ν (E n) ≤ ENNReal.ofReal A * q ^ n := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
    have hreal : A * Real.exp (-(B * n)) = A * (Real.exp (-B)) ^ n := by
      rw [← Real.exp_nat_mul]
      congr 2
      ring
    simpa only [Measure.real_def, E, q, hreal, ENNReal.ofReal_mul hA.le, ENNReal.ofReal_pow (Real.exp_pos _).le]
      using ENNReal.ofReal_le_ofReal (htail n)
  have hsum : (∑' n, environmentLaw ν (E n)) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hEn)
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.inv_ne_top.mpr (tsub_pos_of_lt hq).ne')
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  exact hω.mono fun n hn => lt_of_not_ge hn

/-- Bounded-below expected half-line rates give an almost-sure constant
speed. The speed is the greatest lower bound of the actual expected rates. -/
theorem exists_constant_halfLineEdge_speed_of_bddBelow (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hν : 0 < ν {1})
    (hbd : BddBelow (Set.range fun n : ℕ =>
      (∫ ω, (halfLineEdge ω (n + 1) : ℝ) ∂environmentLaw ν) / ((n : ℝ) + 1))) :
    ∃ β : ℝ, IsGLB (Set.range fun n : ℕ =>
      (∫ ω, (halfLineEdge ω (n + 1) : ℝ) ∂environmentLaw ν) / ((n : ℝ) + 1)) β ∧
      ∀ᵐ ω ∂environmentLaw ν,
        Tendsto (fun n : ℕ => (halfLineEdge ω n : ℝ) / (n : ℝ)) atTop (𝓝 β) := by
  obtain ⟨β, hβ, limit, hInt, hLim, hE⟩ := exists_halfLineEdge_limit_of_bddBelow ν hν hbd
  let c (j : ℕ) : ℝ := β + 1 / ((j : ℝ) + 1)
  have hc (j : ℕ) : β < c j := lt_add_of_pos_right _ (by positivity)
  have hbound : ∀ᵐ ω ∂environmentLaw ν, limit ω ≤ β := by
    have hcaps := ae_all_iff.mpr (fun j => ae_eventually_halfLineEdge_lt_of_isGLB ν hν (hc j) hβ)
    filter_upwards [hcaps, hLim] with ω hω hlim
    have hle (j : ℕ) : limit ω ≤ c j := by
      apply le_of_tendsto hlim
      filter_upwards [hω j, eventually_ge_atTop 1] with n hn hn1
      have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.succ_le_iff.mp hn1)
      exact le_of_lt ((div_lt_iff₀ hn0).mpr hn)
    have ht : Tendsto c atTop (𝓝 β) := by
      simpa only [c, add_zero] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add β
    exact le_of_tendsto_of_tendsto tendsto_const_nhds ht (Eventually.of_forall hle)
  have hnonneg : 0 ≤ᵐ[environmentLaw ν] (fun ω => β - limit ω) :=
    hbound.mono fun ω hω => sub_nonneg.mpr hω
  have hdiff := (integrable_const β).sub hInt
  have hzero : ∫ ω, (β - limit ω) ∂environmentLaw ν = 0 := by
    rw [integral_sub (integrable_const β) hInt, integral_const, probReal_univ,
      one_smul, hE, sub_self]
  have heq := (integral_eq_zero_iff_of_nonneg_ae hnonneg hdiff).mp hzero
  refine ⟨β, hβ, ?_⟩
  filter_upwards [heq, hLim] with ω hω hlim
  have hlimβ : β = limit ω := sub_eq_zero.mp hω
  rwa [hlimβ]

end LPPDifferentiability.FinalDraft
