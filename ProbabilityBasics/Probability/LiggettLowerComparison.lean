/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.LiggettStationaryLimit
public import ProbabilityBasics.Probability.LiggettTestOrder
public import ProbabilityBasics.Probability.SequenceLiminf
public import ProbabilityBasics.Probability.BirkhoffL1

/-! # Liggett's stationary lower comparison

The stationary increment law supplies one integrable Birkhoff limit whose closed
real upper tails are dominated by the extended-real origin lower limit. This is the
lower comparison following (2.14) of Liggett (1985), not the completed subadditive
ergodic theorem.
-/

public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace LPPDifferentiability

/-- From the moment, lower expectation, origin subadditivity, and adjacent
whole-column hypotheses of Liggett's theorem, construct one common finite expected
rate and one measurable integrable comparison variable. No block stationarity
or finiteness of the origin lower limit is needed. -/
theorem exists_liggett_lower_comparison {Ω : Type*} [MeasurableSpace Ω]
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
    ∃ γ : ℝ, ∃ κ : ProbabilityMeasure (ℕ → ℝ), ∃ Y : (ℕ → ℝ) → ℝ,
      Tendsto (fun n : ℕ => (∫ ω, A 0 (n + 1) ω ∂μ) / ((n + 1 : ℕ) : ℝ))
        atTop (𝓝 γ) ∧
      γ = sInf (range (fun n : ℕ =>
        (∫ ω, A 0 (n + 1) ω ∂μ) / ((n + 1 : ℕ) : ℝ))) ∧
      Measurable Y ∧ Integrable Y (κ : Measure (ℕ → ℝ)) ∧
      γ ≤ ∫ z, Y z ∂(κ : Measure (ℕ → ℝ)) ∧
      ∀ a : ℝ, (κ : Measure (ℕ → ℝ)) {z | a ≤ Y z} ≤
        μ {ω | (a : EReal) ≤
          liminf (fun j => ((A 0 (j + 1) ω / (j + 1) : ℝ) : EReal)) atTop} := by
  obtain ⟨γ, κ, r, hγ, hγinf, _hr, hκ, hshift, hcoord⟩ :=
    exists_liggett_stationary_increment_limit μ A hm hi c hlower hsub hadj
  obtain ⟨Y, hYm, hYi, hYconv, _hYinv, hYmean, _hYL1⟩ :=
    exists_birkhoffL1 hshift (measurable_pi_apply 0) (hcoord 0).1
  have hcol : ∀ l, 0 < l → IdentDistrib
      (fun ω => fun k : ℕ => A l (l + k + 1) ω)
      (fun ω => fun k : ℕ => A 0 (k + 1) ω) μ μ := by
    intro l _hl
    simpa only [Nat.add_assoc] using liggett_column_identDistrib A hm hadj l
  have hYlim : ∀ᵐ z ∂(κ : Measure (ℕ → ℝ)),
      liminf (fun j => ((sequencePartialSums z j / (j + 1) : ℝ) : EReal)) atTop =
        (Y z : EReal) := by
    filter_upwards [hYconv] with z hz
    exact normalized_liminf_sequencePartialSums_eq_of_tendsto z (Y z) hz
  refine ⟨γ, κ, Y, hγ, hγinf, hYm, hYi, ?_, ?_⟩
  · rw [hYmean]
    exact (hcoord 0).2
  · intro a
    have horder := measure_liminf_partialSums_le_originColumn μ A hm hsub hcol κ r hκ a
    rw [measure_partialSumsLaw_normalized_liminf,
      measure_originColumnLaw_normalized_liminf] at horder
    have hevent : (κ : Measure (ℕ → ℝ)) {z | a ≤ Y z} =
        (κ : Measure (ℕ → ℝ)) {z | (a : EReal) ≤
          liminf (fun j => ((sequencePartialSums z j / (j + 1) : ℝ) : EReal)) atTop} := by
      apply measure_congr
      filter_upwards [hYlim] with z hz
      simp only [hz, EReal.coe_le_coe_iff]
    exact hevent.trans_le horder

end LPPDifferentiability
