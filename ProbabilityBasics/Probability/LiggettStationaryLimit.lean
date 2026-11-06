/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.LiggettExpectedRate
public import ProbabilityBasics.Probability.UniformOriginCompactness
public import ProbabilityBasics.Probability.UniformIncrementTailLaw
public import ProbabilityBasics.Probability.WeakCoordinateMean

/-! # The stationary increment limit from Liggett's array

All domination, common-law, expected-rate, moment, tail and mean inputs of
the construction are discharged from (1.3), (1.7) and (1.8) of Liggett (1985).
Block stationarity (1.9) is not needed for this step. This does not
assert the completed subadditive ergodic theorem.
-/

public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace LPPDifferentiability

/-- Construction from Liggett's array of one finite expected rate and one stationary
weak increment limit. Every limit coordinate is integrable and has mean at
least that same rate. No conclusion of an intermediate helper is assumed. -/
theorem exists_liggett_stationary_increment_limit {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : ℕ → ℕ → Ω → ℝ)
    (hm : ∀ n : ℕ, 0 < n → Measurable (A 0 n))
    (hi : ∀ n : ℕ, 0 < n → Integrable (A 0 n) μ)
    (c : ℝ)
    (hlower : ∀ n : ℕ, 0 < n → -(c * (n : ℝ)) ≤ ∫ ω, A 0 n ω ∂μ)
    (hsub : ∀ m n : ℕ, 0 < m → m < n →
      ∀ᵐ ω ∂μ, A 0 n ω ≤ A 0 m ω + A m n ω)
    (hadj : ∀ m : ℕ,
      IdentDistrib (fun ω (k : ℕ) => A (m + 1) (m + 1 + (k + 1)) ω)
        (fun ω (k : ℕ) => A m (m + (k + 1)) ω) μ μ) :
    ∃ γ : ℝ, ∃ κ : ProbabilityMeasure (ℕ → ℝ), ∃ r : ℕ → ℕ,
      Tendsto (fun n : ℕ => (∫ ω, A 0 (n + 1) ω ∂μ) / ((n + 1 : ℕ) : ℝ))
        atTop (𝓝 γ) ∧
      γ = sInf (range (fun n : ℕ =>
        (∫ ω, A 0 (n + 1) ω ∂μ) / ((n + 1 : ℕ) : ℝ))) ∧
      StrictMono r ∧
      Tendsto (fun i => uniformOriginIncrementLaw μ (A 0) hm (r i)) atTop (𝓝 κ) ∧
      MeasurePreserving sequenceShift (κ : Measure (ℕ → ℝ)) (κ : Measure (ℕ → ℝ)) ∧
      ∀ k : ℕ, Integrable (fun z : ℕ → ℝ => z k) (κ : Measure (ℕ → ℝ)) ∧
        γ ≤ ∫ z : ℕ → ℝ, z k ∂(κ : Measure (ℕ → ℝ)) := by
  obtain ⟨γ, hγ, hγinf⟩ := exists_liggett_expected_rate A hm hi c hlower hsub hadj
  let X : ℕ → Ω → ℝ := A 0
  let Z : ℕ → Ω → ℝ := fun j => A j (j + 1)
  let g : Ω → ℝ := A 0 1
  have hdom : ∀ j, 0 < j → ∀ᵐ ω ∂μ, X (j + 1) ω - X j ω ≤ Z j ω := by
    intro j hj
    filter_upwards [hsub j (j + 1) hj (by omega)] with ω hω
    exact sub_le_iff_le_add'.mpr hω
  have hlaw : ∀ j, 0 < j → IdentDistrib (Z j) g μ μ := by
    intro j _hj
    exact liggett_block_identDistrib A hm hadj j 1 (by omega)
  have hg : Integrable g μ := hi 1 (by omega)
  have hγ' : Tendsto (fun n : ℕ => (∫ ω, X (n + 1) ω ∂μ) / (n + 1 : ℝ))
      atTop (𝓝 γ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hγ
  obtain ⟨κ, r, hr, hκ, hshift⟩ := exists_stationary_uniformOriginIncrementLaw_subsequence
    μ μ X Z g hdom hlaw hg hm hi γ hγ'
  refine ⟨γ, κ, r, hγ, hγinf, hr, hκ, hshift, fun k => ?_⟩
  obtain ⟨C, hC⟩ := exists_integral_abs_uniformOriginIncrement_bound
    μ μ X Z g hdom hlaw hg hm hi γ hγ' k
  have hbound (i : ℕ) :
      (∫ z : ℕ → ℝ, |z k|
        ∂(uniformOriginIncrementLaw μ X hm (r i) : Measure (ℕ → ℝ))) ≤ C := by
    rw [integral_abs_uniformOriginIncrementLaw_eval]
    exact hC (r i)
  have hint (i : ℕ) := integrable_uniformOriginIncrementLaw_eval μ X hm hi (r i) k
  have hk := integrable_coordinate_of_weak_abs_integral_le
    (fun i => uniformOriginIncrementLaw μ X hm (r i)) κ hκ k hint C hbound
  refine ⟨hk, ?_⟩
  apply coordinate_mean_le_of_weak_abs_integral_le_pos_tails
    (fun i => uniformOriginIncrementLaw μ X hm (r i)) κ hκ k hint C hbound
  · intro ε hε
    obtain ⟨R, _hR, htail⟩ := uniformOriginIncrementLaw_positiveTail_uniform
      μ μ X Z g hdom hlaw hg hm hi ε hε
    exact ⟨R, fun i => htail R le_rfl (r i) k⟩
  · exact (tendsto_integral_uniformOriginIncrementLaw_eval μ X hm hi γ hγ' k).comp
      hr.tendsto_atTop

end LPPDifferentiability
