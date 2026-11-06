/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.LiggettExpectedRate
public import ProbabilityBasics.Probability.StationaryAverages

/-! # Block averages in Liggett's stationary argument

For each positive block length, the stationary law starts after the first
block. The initial block is retained; its mean is matched to the first
tail block by the whole-column law.
-/

public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators

namespace LPPDifferentiability

/-- Averages of adjacent length-`k` blocks converge on the original
experiment. The initial block need not belong to the stationary tail law.
Every finite average is integrable, and the limit mean is the origin mean. -/
theorem exists_liggett_block_average {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (A : ℕ → ℕ → Ω → ℝ)
    (hmeas : ∀ n : ℕ, 0 < n → Measurable (A 0 n))
    (hint : ∀ n : ℕ, 0 < n → Integrable (A 0 n) μ)
    (hadj : ∀ m : ℕ,
      IdentDistrib (fun ω (j : ℕ) => A (m + 1) (m + 1 + (j + 1)) ω)
        (fun ω (j : ℕ) => A m (m + (j + 1)) ω) μ μ)
    (k : ℕ) (hk : 0 < k)
    (hstat : IdentDistrib
      (fun ω (j : ℕ) => A ((j + 2) * k) ((j + 3) * k) ω)
      (fun ω (j : ℕ) => A ((j + 1) * k) ((j + 2) * k) ω) μ μ) :
    ∃ U : Ω → ℝ, Integrable U μ ∧
      (∀ q : ℕ, Integrable (fun ω =>
        (∑ i ∈ Finset.range q, A (i * k) ((i + 1) * k) ω) / (q : ℝ)) μ) ∧
      (∀ᵐ ω ∂μ, Tendsto (fun q : ℕ =>
        (∑ i ∈ Finset.range q, A (i * k) ((i + 1) * k) ω) / (q : ℝ))
        atTop (𝓝 (U ω))) ∧
      (∫ ω, U ω ∂μ) = ∫ ω, A 0 k ω ∂μ ∧
      Tendsto (fun q : ℕ => ∫ ω,
        |(∑ i ∈ Finset.range q, A (i * k) ((i + 1) * k) ω) / (q : ℝ) - U ω| ∂μ)
        atTop (𝓝 0) := by
  let C : Ω → ℕ → ℝ := fun ω i => A (i * k) ((i + 1) * k) ω
  have h0 : Integrable (fun ω => C ω 0) μ := by
    simpa [C] using hint k hk
  have hblock := liggett_block_integrable_integral A hmeas hint hadj k k hk
  have h1 : Integrable (fun ω => C ω 1) μ := by
    simpa [C, Nat.succ_mul] using hblock.1
  have hblock_mean : (∫ ω, C ω 1 ∂μ) = ∫ ω, A 0 k ω ∂μ := by
    simpa [C, Nat.succ_mul] using hblock.2
  have htail_left (ω : Ω) :
      sequenceShift (sequenceShift (C ω)) =
        (fun j : ℕ => A ((j + 2) * k) ((j + 3) * k) ω) := by
    funext j
    calc
      sequenceShift (sequenceShift (C ω)) j = ((sequenceShift^[2]) (C ω)) j := by rfl
      _ = C ω (j + 2) := sequenceShift_iterate_apply (C ω) 2 j
      _ = A ((j + 2) * k) ((j + 3) * k) ω := by
        simp only [C]
  have htail_right (ω : Ω) :
      sequenceShift (C ω) =
        (fun j : ℕ => A ((j + 1) * k) ((j + 2) * k) ω) := by
    funext j
    calc
      sequenceShift (C ω) j = ((sequenceShift^[1]) (C ω)) j := by rfl
      _ = C ω (j + 1) := sequenceShift_iterate_apply (C ω) 1 j
      _ = A ((j + 1) * k) ((j + 2) * k) ω := by
        simp only [C]
  have htail : IdentDistrib
      (fun ω => sequenceShift (sequenceShift (C ω)))
      (fun ω => sequenceShift (C ω)) μ μ := by
    rw [show (fun ω => sequenceShift (sequenceShift (C ω))) =
      (fun ω j => A ((j + 2) * k) ((j + 3) * k) ω) by funext ω; exact htail_left ω]
    rw [show (fun ω => sequenceShift (C ω)) =
      (fun ω j => A ((j + 1) * k) ((j + 2) * k) ω) by funext ω; exact htail_right ω]
    exact hstat
  obtain ⟨U, hU, hfinite, hconv, hmean, hL1⟩ :=
    exists_tail_stationary_sequence_average μ C htail h0 h1
  have hbridge (q : ℕ) (ω : Ω) :
      (∑ i ∈ Finset.range q, A (i * k) ((i + 1) * k) ω) / (q : ℝ) =
        birkhoffAverage ℝ sequenceShift (fun z : ℕ → ℝ => z 0) q (C ω) := by
    simpa only [C] using (birkhoffAverage_sequenceShift_eval_zero (C ω) q).symm
  have haverage_integrable (q : ℕ) : Integrable (fun ω =>
      (∑ i ∈ Finset.range q, A (i * k) ((i + 1) * k) ω) / (q : ℝ)) μ := by
    exact (hfinite q).congr
      (Eventually.of_forall (fun ω => (hbridge q ω).symm))
  have haverage_converges : ∀ᵐ ω ∂μ, Tendsto (fun q : ℕ =>
      (∑ i ∈ Finset.range q, A (i * k) ((i + 1) * k) ω) / (q : ℝ))
      atTop (𝓝 (U ω)) := by
    filter_upwards [hconv] with ω hω
    exact hω.congr' (Eventually.of_forall (fun q => (hbridge q ω).symm))
  have haverage_mean : (∫ ω, U ω ∂μ) = ∫ ω, A 0 k ω ∂μ := by
    exact hmean.trans hblock_mean
  have herror (q : ℕ) :
      (∫ ω,
        |birkhoffAverage ℝ sequenceShift (fun z : ℕ → ℝ => z 0) q (C ω) - U ω| ∂μ) =
      (∫ ω,
        |(∑ i ∈ Finset.range q, A (i * k) ((i + 1) * k) ω) / (q : ℝ) - U ω| ∂μ) := by
    apply integral_congr_ae
    filter_upwards [] with ω
    rw [← hbridge q ω]
  have haverage_L1 : Tendsto (fun q : ℕ => ∫ ω,
      |(∑ i ∈ Finset.range q, A (i * k) ((i + 1) * k) ω) / (q : ℝ) - U ω| ∂μ)
      atTop (𝓝 0) := by
    exact hL1.congr' (Eventually.of_forall herror)
  exact ⟨U, hU, haverage_integrable, haverage_converges, haverage_mean, haverage_L1⟩

end LPPDifferentiability
