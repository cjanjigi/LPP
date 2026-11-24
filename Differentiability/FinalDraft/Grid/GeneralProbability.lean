/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.Probability.GridCoarseGoodProbability
import Differentiability.Analysis.GridScaleCounts
import Differentiability.Analysis.GridScaleSums
import Differentiability.Probability.GridGoodEvent
import Mathlib.Tactic

/-! # Probability of the general-weight grid cell conditions -/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace LPPDifferentiability

/-- The tail in the general-weight grid probability bound
(Appendix B item `ch:prob`). -/
noncomputable def generalGridBeta (A R q0 : ℝ) (J : ℕ) : ℝ :=
  ((4 * (A + 4) + 1) * (2 * R + 2)) *
    ∑' i : ℕ, (2 : ℝ) ^ (5 * (i + J)) * Real.exp (-(q0 / 2 * ((i + J : ℕ) : ℝ) ^ 2))

/-- The general-weight grid tail tends to zero and depends only on the
extent, width, and crossing probability (Appendix B item `ch:prob`). -/
theorem general_grid_beta_tendsto (A R q0 : ℝ) :
    Tendsto (generalGridBeta A R q0) atTop (𝓝 0) :=
  grid_beta_tendsto (q0 / 2) _

/-- The general-weight grid tail is positive at each scale cutoff
(Appendix B item `ch:prob`). -/
theorem general_grid_beta_pos {A R q0 : ℝ} (hA : 0 < A) (hR : 0 < R) (hq0 : 0 < q0)
    (J : ℕ) : 0 < generalGridBeta A R q0 J :=
  grid_beta_pos (by positivity) (by positivity) J

/-- All general-weight cell failures cost at most the source tail
(`differentiability_final_draft.tex`, Section 6 parallelogram argument and Appendix B item `ch:prob`).
The heavy-site cutoff estimate is uniform over every cell of the scale. -/
theorem general_grid_cells_failure_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {p : ℝ} (hp : 4 < p)
    (hmom : (∫⁻ x, ENNReal.ofReal ((max x 0) ^ p) ∂μ) < ∞)
    (a G K cstar A R q0 : ℝ) (hcstar : 1 ≤ cstar) (hA : 0 < A) (hR : 0 < R) (hq0 : 0 < q0)
    (k0 k J mk : ℕ) (hk0pos : 0 < k0) (hk : 4 * k0 + 3 ≤ k) (hJ : 1 ≤ J) (hmk : mk ≤ 3 * k)
    (htrial : ∀ j : ℕ, j ≤ ⌈((mk : ℝ) - 1) / 4⌉₊ →
      (∀ n : ℕ, 1 ≤ n → (n : ℝ) < (2 : ℝ) ^ (mk - 4 * j - 1) →
        q0 < (environmentLaw μ).real {ω : Environment |
          ∃ u : Lattice, u.1 + u.2 = 0 ∧ ∃ e : ℕ × ℕ, e.1 + e.2 = n ∧ ∃ q : Path u e,
            (∀ i, |(1 - a) * ((q.vertex i).1 : ℝ) - a * ((q.vertex i).2 : ℝ)| ≤
              8 * (2 : ℝ) ^ (k - j)) ∧
            G * (n : ℝ) - K * (2 : ℝ) ^ (k - j) < pathWeight ω q}) ∧
      (1 < (2 : ℝ) ^ (mk - 4 * j - 1) →
        (2 : ℝ) ^ (mk - 4 * j - 1) ≤ ((2 : ℝ) ^ (k - j)) ^ 3 / 2))
    (hsmall : 17 * (∫ x : ℝ, (max x 0) ^ p ∂μ) *
      (2 : ℝ) ^ (-(p - 4) * ((k : ℝ) - 3) / 4) ≤ q0 / 2) :
    (environmentLaw μ).real (generalGridCellsGood a G K cstar A R k J mk)ᶜ ≤
      generalGridBeta A R q0 J := by
  classical
  let jstar : ℕ := ⌈((mk : ℝ) - 1) / 4⌉₊
  let C : ℝ := (4 * (A + 4) + 1) * (2 * R + 2)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  choose S hS using fun j : ℕ => exists_finset_int_of_bounded
    (fun I => ((2 ^ (mk - 4 * j - 1) : ℕ) : ℤ) ∣ I ∧ |(I : ℝ)| ≤ (A + 4) * 2 ^ mk)
    ((A + 4) * 2 ^ mk) (fun I hI => hI.2)
  choose B hB using fun j : ℕ => exists_finset_int_of_bounded
    (fun h => ∃ ρ : ℝ, (h : ℝ) * 2 ^ (k - j) ≤ ρ ∧
      ρ < ((h : ℝ) + 1) * 2 ^ (k - j) ∧ |ρ| ≤ R * 2 ^ k)
    (R * 2 ^ k + 1) (fun h ⟨ρ, h₁, h₂, h₃⟩ =>
      abs_bin_le (by positivity) (one_le_pow₀ (by norm_num)) h₁ h₂ h₃)
  let Bad (j : ℕ) (I h : ℤ) :=
    (generalGridCellGood a G K cstar I h (2 ^ (mk - 4 * j - 1)) j (2 ^ (k - j)))ᶜ
  have heq : (generalGridCellsGood a G K cstar A R k J mk)ᶜ =
      ⋃ j ∈ Finset.Icc J jstar, ⋃ I ∈ S j, ⋃ h ∈ B j, Bad j I h := by
    ext ω
    simp only [generalGridCellsGood, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall,
      Set.mem_iUnion, exists_prop, Finset.mem_Icc, hS, hB, Bad, jstar]
    constructor
    · rintro ⟨j, hJj, hj, I, hdiv, hI, h, hh, hω⟩
      exact ⟨j, ⟨hJj, hj⟩, I, ⟨hdiv, hI⟩, h, hh, hω⟩
    · rintro ⟨j, ⟨hJj, hj⟩, I, ⟨hdiv, hI⟩, h, hh, hω⟩
      exact ⟨j, hJj, hj, I, hdiv, hI, h, hh, hω⟩
  have hBad : ∀ j ∈ Finset.Icc J jstar, ∀ I ∈ S j, ∀ h ∈ B j,
      (environmentLaw μ).real (Bad j I h) ≤ Real.exp (-(q0 / 2 * (j : ℝ) ^ 2)) := by
    intro j hj I _ h _
    obtain ⟨hJj, hjstar⟩ := Finset.mem_Icc.1 hj
    obtain ⟨-, hjk, -, -⟩ := grid_scale_index_bounds (rfl : jstar = _) hmk hk hk0pos hjstar
    have hjBound := (grid_jstar_bounds (m := mk) (rfl : jstar = _)).2
    have hk4 : k ≤ 4 * (k - j) + 3 := by omega
    dsimp only [Bad]
    by_cases hcoarse : 8 * cstar * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ)) ≤
        ((2 ^ (mk - 4 * j - 1) : ℕ) : ℝ)
    · exact fixed_coarse_good_event_prob_le μ hp hmom a G K cstar q0 hcstar k j mk (hJ.trans hJj)
        hk4 hcoarse (htrial j hjstar).2 (htrial j hjstar).1 hsmall I h
    · rw [generalGridCellGood, ite_eq_right hcoarse, Set.compl_univ, measureReal_empty]
      exact (Real.exp_pos _).le
  have hcard : ∀ j ∈ Finset.Icc J jstar,
      ((S j).card : ℝ) * ((B j).card : ℝ) ≤ C * 2 ^ (5 * j) := by
    intro j hj
    obtain ⟨-, hjstar⟩ := Finset.mem_Icc.1 hj
    obtain ⟨-, hjk, -, -⟩ := grid_scale_index_bounds (rfl : jstar = _) hmk hk hk0pos hjstar
    have hCountS := (grid_count_le hA mk j (S j) (hS j)).2
    have hCountB := (grid_bin_count_le hR hjk (B j) (hB j)).2
    calc
      ((S j).card : ℝ) * ((B j).card : ℝ) ≤
        ((4 * (A + 4) + 1) * 2 ^ (4 * j)) * ((2 * R + 2) * 2 ^ j) :=
        mul_le_mul hCountS hCountB (Nat.cast_nonneg _) (by positivity)
      _ = C * 2 ^ (5 * j) := by
        dsimp only [C]
        rw [show 5 * j = 4 * j + j by ring, pow_add]
        ring
  rw [heq]
  exact (grid_union_measure_le (environmentLaw μ) J jstar S B Bad _ hBad).trans
    (grid_scale_tail_le hq0 hC J jstar S B hcard)

end LPPDifferentiability
