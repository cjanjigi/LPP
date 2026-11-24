/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.FlatClassificationSource.WeightedWhiteBlocks
public import Differentiability.FinalDraft.FlatClassificationSource.WeightedCoarsePaths
import all Differentiability.Probability.TopPassageDecay
import Mathlib.Tactic

/-! # Exponential decay of near-optimal original-weight passages -/

public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace LPPDifferentiability.FinalDraft

/-- A positive Bernoulli parameter gives positive mass at one. -/
theorem bernoulli_one_pos_of_density_pos (q : unitInterval) (hq : 0 < (q : ℝ)) :
    0 < bernoulliMeasure (1 : ℝ) 0 q {1} := by
  rw [bernoulliMeasure_apply_of_mem_of_notMem q (measurableSet_singleton _) (by simp) (by simp),
    ENNReal.coe_nnreal_eq, unitInterval.coe_toNNReal]
  exact ENNReal.ofReal_pos.mpr hq

/-- A single near-top threshold whose mean half-line edge is below the crossing speed gives
exponential decay for the original last-passage times. -/
theorem weighted_passage_beyond_edge_decay (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hle : ∀ᵐ w ∂ν, w ≤ 1) (δ : ℝ) (hδ : 0 < δ) (hq : 0 < (nearTopDensity ν δ : ℝ))
    (c₁ : ℝ) (L : ℕ) (hL : 0 < L)
    (hc : ∫ ω, (halfLineEdge ω L : ℝ) ∂environmentLaw
      (bernoulliMeasure (1 : ℝ) 0 (nearTopDensity ν δ)) < c₁ * L)
    (s : ℝ) (hc₁s : c₁ < s) (hs₁ : s ≤ 1) :
    ∃ ε A B : ℝ, 0 < ε ∧ 0 < A ∧ 0 < B ∧ ∀ k ℓ : ℕ, s * (k + ℓ) ≤ k →
      (environmentLaw ν).real {ω | (1 - ε) * (k + ℓ) ≤ lastPassage ω 0 (k, ℓ)} ≤
        A * Real.exp (-(B * (k + ℓ))) := by
  classical
  have hc₁1 : c₁ < 1 := hc₁s.trans_le hs₁
  have h1c₁ : 0 < 1 - c₁ := by linarith
  let q := nearTopDensity ν δ
  let κ := bernoulliMeasure (1 : ℝ) 0 q
  have hq₁ : 0 < κ {1} := bernoulli_one_pos_of_density_pos q hq
  obtain ⟨A₃, B₃, -, hB₃, h3⟩ := halfLineEdge_upper_deviation κ hq₁ c₁ L hL hc
  -- the black density `ρ` between `r = (1 - s) / (1 - c₁)` and `1`
  obtain ⟨r, hr1, hrdef⟩ : ∃ r : ℝ, r < 1 ∧ r = (1 - s) / (1 - c₁) := by
    refine ⟨(1 - s) / (1 - c₁), ?_, rfl⟩
    rw [div_lt_one h1c₁]
    linarith
  have hr0 : 0 ≤ r := by
    rw [hrdef]
    exact div_nonneg (by linarith) h1c₁.le
  obtain ⟨ρ, hρ0, hρ1, hrρ⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ r < ρ :=
    ⟨(1 + r) / 2, by linarith, by linarith, by linarith⟩
  have hη : 0 < ρ - r := sub_pos.2 hrρ
  -- the sparse-path lemma with separation 2
  obtain ⟨ζ, hζ0, -, hN4⟩ := exists_sparse_good_coarse_path_cutoff ρ hρ0 hρ1 2
  obtain ⟨N, hNpos, hNζ⟩ := exists_scale (A₃ / (q : ℝ)) B₃ ζ hB₃ hζ0
  have hwhite : ∀ v : ℕ × ℕ, (environmentLaw ν).real
      {ω : Environment | ¬ IsBlackPassageBlock ω N c₁ δ ((v.1 : ℤ), (v.2 : ℤ))} ≤ ζ := by
    intro v
    refine (white_passage_block_probability_le ν hle N c₁ δ _ hq).trans ?_
    calc
      _ ≤ ((N : ℝ) + 1) * (A₃ * Real.exp (-(B₃ * N))) / (q : ℝ) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (h3 N) (by positivity)) hq.le
      _ = ((N : ℝ) + 1) * ((A₃ / (q : ℝ)) * Real.exp (-(B₃ * N))) := by ring
      _ ≤ _ := hNζ
  obtain ⟨a, b, ha, hb, hab⟩ := hN4 (environmentLaw ν)
    (fun v : ℕ × ℕ => {ω : Environment |
      IsBlackPassageBlock ω N c₁ δ ((v.1 : ℤ), (v.2 : ℤ))})
    (fun v => measurableSet_isBlackPassageBlock N c₁ δ _) hwhite
    (iIndepSet_isBlackPassageBlock ν N hNpos c₁ δ)
  have hω : ∀ᵐ ω ∂environmentLaw ν, ∀ x : Lattice, ω x ≤ 1 := ae_all_iff.mpr fun x =>
    ae_of_ae_map (measurable_environment_eval x).aemeasurable
      (by rwa [environmentLaw_map_eval ν x])
  -- the constants of the conclusion
  obtain ⟨n₀, hn₀1, hn₀2⟩ : ∃ n₀ : ℕ, 3 * N ≤ n₀ ∧ 4 * (N : ℝ) / (ρ - r) ≤ n₀ :=
    ⟨⌈4 * (N : ℝ) / (ρ - r)⌉₊ + 3 * N, by omega,
      le_trans (Nat.le_ceil _) (by exact_mod_cast Nat.le_add_right _ _)⟩
  let ε := δ * ((ρ - r) / (4 * N))
  have hε : 0 < ε := mul_pos hδ (div_pos hη (by positivity))
  refine ⟨ε, max (a * Real.exp (3 * b)) (Real.exp (b / (N : ℝ) * (n₀ : ℝ))),
    b / N, hε, lt_max_of_lt_left (by positivity), by positivity, ?_⟩
  intro k ℓ hks
  have hBpos : 0 < b / (N : ℝ) := by positivity
  by_cases hn : n₀ ≤ k + ℓ
  · -- large `k + ℓ`: use the coarse-path bound
    have h3N : 3 * N ≤ k + ℓ := le_trans hn₀1 hn
    have hQ3 : 3 ≤ (k + ℓ) / N := (Nat.le_div_iff_mul_le hNpos).2 h3N
    have hM1 : 1 ≤ (k + ℓ) / N - 2 := by omega
    have hn₀' : 4 * (N : ℝ) / (ρ - r) ≤ (k : ℝ) + ℓ := le_trans hn₀2 (by exact_mod_cast hn)
    have hbound := budget_le N k ℓ hNpos s c₁ ρ r hρ0 hρ1 hrdef hη hn₀' h3N
    have hfl : ((k : ℝ) + ℓ) / N - 3 < (((k + ℓ) / N - 2 : ℕ) : ℝ) := by
      have h := floor_div_bounds (k + ℓ) N hNpos h3N
      rw [Nat.cast_add] at h
      exact h
    have hP := hab ((k + ℓ) / N - 2) hM1
    have hincl : (environmentLaw ν).real
        {ω | (1 - ε) * (k + ℓ) ≤ lastPassage ω 0 (k, ℓ)} ≤
        a * Real.exp (-(b * (((k + ℓ) / N - 2 : ℕ) : ℝ))) := by
      refine le_trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)) hP
      filter_upwards [hω] with ω hω hG
      obtain ⟨q, hq0, hqs, hqc⟩ := coarse_path_few_black_passage_blocks ω hω N hNpos c₁ s δ ε
        hc₁1 hδ k ℓ hks h3N hG
      have hεeq : ε * ((k : ℝ) + ℓ) / δ = (ρ - r) / (4 * N) * ((k : ℝ) + ℓ) := by
        dsimp only [ε]
        rw [mul_assoc, mul_div_cancel_left₀ _ hδ.ne']
      rw [hεeq] at hqc
      refine ⟨q, hq0, hqs, ?_⟩
      refine le_trans (le_of_eq (congrArg (Nat.cast : ℕ → ℝ) ?_)) (le_trans hqc ?_)
      · refine card_filter_congr ?_
        intro j
        exact Iff.rfl
      · linarith
    refine le_trans hincl ?_
    refine le_trans (exp_tail a b N ((k : ℝ) + ℓ) _ ha hb hfl) ?_
    have hmax := le_max_left (a * Real.exp (3 * b)) (Real.exp (b / (N : ℝ) * (n₀ : ℝ)))
    exact mul_le_mul_of_nonneg_right hmax (Real.exp_pos _).le
  · -- small `k + ℓ`: the probability is at most one and the constant is large
    have hlt : k + ℓ < n₀ := lt_of_not_ge hn
    have hkn₀ : (k : ℝ) + ℓ ≤ n₀ := by exact_mod_cast hlt.le
    have h1 : 1 ≤ Real.exp (b / (N : ℝ) * (n₀ : ℝ)) *
        Real.exp (-(b / (N : ℝ) * ((k : ℝ) + ℓ))) := by
      rw [← Real.exp_add]
      refine Real.one_le_exp ?_
      rw [← sub_eq_add_neg]
      exact sub_nonneg.2 (mul_le_mul_of_nonneg_left hkn₀ hBpos.le)
    refine le_trans measureReal_le_one ?_
    refine le_trans h1 ?_
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

end LPPDifferentiability.FinalDraft
