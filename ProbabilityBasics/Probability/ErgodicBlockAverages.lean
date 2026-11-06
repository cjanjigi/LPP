/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.LiggettBlockAverages
public import ProbabilityBasics.Probability.SequenceAverages
public import Mathlib.Dynamics.Ergodic.Function
import ProbabilityBasics.Probability.BirkhoffErgodic

/-! # Ergodic limits of actual block averages

Ergodicity is assumed for the actual positive-index block process under its
own pushed law. The first block is retained in the full averages.
-/

public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators

namespace LPPDifferentiability

/-- If the actual positive-index length-`k` block process is ergodic under
its pushed law, the full block averages converge almost surely and in L1 to
the origin-block mean. Every finite average is integrable. -/
theorem ae_tendsto_liggett_block_average_of_ergodic
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (A : ℕ → ℕ → Ω → ℝ)
    (hmeas : ∀ n : ℕ, 0 < n → Measurable (A 0 n))
    (hint : ∀ n : ℕ, 0 < n → Integrable (A 0 n) μ)
    (hadj : ∀ m : ℕ,
      IdentDistrib (fun ω (j : ℕ) => A (m + 1) (m + 1 + (j + 1)) ω)
        (fun ω (j : ℕ) => A m (m + (j + 1)) ω) μ μ)
    (k : ℕ) (hk : 0 < k)
    (hstat : IdentDistrib
      (fun ω (j : ℕ) => A ((j + 2) * k) ((j + 3) * k) ω)
      (fun ω (j : ℕ) => A ((j + 1) * k) ((j + 2) * k) ω) μ μ)
    (hErg : Ergodic sequenceShift
      (μ.map (fun ω (j : ℕ) => A ((j + 1) * k) ((j + 2) * k) ω))) :
    (∀ q : ℕ, Integrable (fun ω =>
      (∑ i ∈ Finset.range q, A (i * k) ((i + 1) * k) ω) / (q : ℝ)) μ) ∧
    (∀ᵐ ω ∂μ, Tendsto (fun q : ℕ =>
      (∑ i ∈ Finset.range q, A (i * k) ((i + 1) * k) ω) / (q : ℝ))
      atTop (𝓝 (∫ ω, A 0 k ω ∂μ))) ∧
    Tendsto (fun q : ℕ => ∫ ω,
      |(∑ i ∈ Finset.range q, A (i * k) ((i + 1) * k) ω) / (q : ℝ) -
        (∫ ω, A 0 k ω ∂μ)| ∂μ) atTop (𝓝 0) := by
  let B : Ω → ℕ → ℝ := fun ω j => A ((j + 1) * k) ((j + 2) * k) ω
  have hB : AEMeasurable B μ := hstat.aemeasurable_snd
  let κ : ProbabilityMeasure (ℕ → ℝ) :=
    ⟨μ.map B, (Measure.isProbabilityMeasure_map_iff hB).2 inferInstance⟩
  have hblock := liggett_block_integrable_integral A hmeas hint hadj k k hk
  have hB0 : Integrable (fun ω => B ω 0) μ := by
    simpa [B, Nat.succ_mul] using hblock.1
  have hcoord : Integrable (fun z : ℕ → ℝ => z 0) (κ : Measure (ℕ → ℝ)) :=
    (integrable_map_measure (measurable_pi_apply 0).aestronglyMeasurable hB).2 hB0
  have hcoordMean : (∫ z, z 0 ∂(κ : Measure (ℕ → ℝ))) =
      ∫ ω, A 0 k ω ∂μ := by
    calc
      (∫ z, z 0 ∂(κ : Measure (ℕ → ℝ))) = ∫ ω, B ω 0 ∂μ :=
        integral_map hB (measurable_pi_apply 0).aestronglyMeasurable
      _ = ∫ ω, A 0 k ω ∂μ := by
        simpa [B, Nat.succ_mul] using hblock.2
  have hTailMapConv := ae_tendsto_birkhoffAverage_integral_of_ergodic
    (μ := (κ : Measure (ℕ → ℝ))) hErg (measurable_pi_apply 0) hcoord
  have hTailConv : ∀ᵐ ω ∂μ, Tendsto
      (fun q : ℕ => birkhoffAverage ℝ sequenceShift
        (fun z : ℕ → ℝ => z 0) q (B ω)) atTop
      (𝓝 (∫ ω, A 0 k ω ∂μ)) := by
    filter_upwards [ae_of_ae_map hB hTailMapConv] with ω hω
    simpa only [hcoordMean] using hω
  let C : Ω → ℕ → ℝ := fun ω i => A (i * k) ((i + 1) * k) ω
  have hshift (ω : Ω) : sequenceShift (C ω) = B ω := by
    funext j
    simp [C, B, sequenceShift]
  have hformula (q : ℕ) (ω : Ω) :
      birkhoffAverage ℝ sequenceShift (fun z : ℕ → ℝ => z 0)
          (q + 1) (C ω) =
        (q : ℝ) / (q + 1 : ℝ) *
          birkhoffAverage ℝ sequenceShift (fun z : ℕ → ℝ => z 0) q (B ω) +
        C ω 0 / (q + 1 : ℝ) := by
    rw [birkhoffAverage_sequenceShift_succ, hshift ω]
  have hcoeff : Tendsto (fun q : ℕ => (q : ℝ) / (q + 1 : ℝ))
      atTop (𝓝 1) := tendsto_natCast_div_add_atTop (1 : ℝ)
  have hsmall (c : ℝ) : Tendsto (fun q : ℕ => c / (q + 1 : ℝ))
      atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, one_mul, mul_zero] using
      (tendsto_const_nhds (x := c)).mul
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hfullBirkhoffConv : ∀ᵐ ω ∂μ, Tendsto
      (fun q : ℕ => birkhoffAverage ℝ sequenceShift
        (fun z : ℕ → ℝ => z 0) q (C ω)) atTop
      (𝓝 (∫ ω, A 0 k ω ∂μ)) := by
    filter_upwards [hTailConv] with ω hω
    apply (tendsto_add_atTop_iff_nat 1).1
    have hh : Tendsto (fun q : ℕ =>
        (q : ℝ) / (q + 1 : ℝ) *
          birkhoffAverage ℝ sequenceShift (fun z : ℕ → ℝ => z 0) q (B ω) +
        C ω 0 / (q + 1 : ℝ)) atTop
        (𝓝 (∫ ω, A 0 k ω ∂μ)) := by
      simpa only [one_mul, add_zero] using (hcoeff.mul hω).add (hsmall (C ω 0))
    exact hh.congr' (Eventually.of_forall (fun q => (hformula q ω).symm))
  have hbridge (q : ℕ) (ω : Ω) :
      (∑ i ∈ Finset.range q, A (i * k) ((i + 1) * k) ω) / (q : ℝ) =
        birkhoffAverage ℝ sequenceShift (fun z : ℕ → ℝ => z 0) q (C ω) := by
    simpa only [C] using
      (birkhoffAverage_sequenceShift_eval_zero (C ω) q).symm
  have hfullConv : ∀ᵐ ω ∂μ, Tendsto (fun q : ℕ =>
      (∑ i ∈ Finset.range q, A (i * k) ((i + 1) * k) ω) / (q : ℝ))
      atTop (𝓝 (∫ ω, A 0 k ω ∂μ)) := by
    filter_upwards [hfullBirkhoffConv] with ω hω
    exact hω.congr' (Eventually.of_forall (fun q => (hbridge q ω).symm))
  obtain ⟨U, _hU, hfinite, hconv, _hmean, hL1⟩ :=
    exists_liggett_block_average A hmeas hint hadj k hk hstat
  have hUeq : U =ᵐ[μ] (fun _ => ∫ ω, A 0 k ω ∂μ) := by
    filter_upwards [hconv, hfullConv] with ω hω hω'
    exact tendsto_nhds_unique hω hω'
  have hdetConv : ∀ᵐ ω ∂μ, Tendsto (fun q : ℕ =>
      (∑ i ∈ Finset.range q, A (i * k) ((i + 1) * k) ω) / (q : ℝ))
      atTop (𝓝 (∫ ω, A 0 k ω ∂μ)) := by
    filter_upwards [hconv, hUeq] with ω hω heq
    simpa only [heq] using hω
  have herror (q : ℕ) :
      (∫ ω, |(∑ i ∈ Finset.range q,
          A (i * k) ((i + 1) * k) ω) / (q : ℝ) -
          (∫ ω, A 0 k ω ∂μ)| ∂μ) =
      (∫ ω, |(∑ i ∈ Finset.range q,
          A (i * k) ((i + 1) * k) ω) / (q : ℝ) - U ω| ∂μ) := by
    apply integral_congr_ae
    filter_upwards [hUeq] with ω hω
    rw [← hω]
  have hdetL1 : Tendsto (fun q : ℕ => ∫ ω,
      |(∑ i ∈ Finset.range q, A (i * k) ((i + 1) * k) ω) / (q : ℝ) -
        (∫ ω, A 0 k ω ∂μ)| ∂μ) atTop (𝓝 0) := by
    exact hL1.congr' (Eventually.of_forall (fun q => (herror q).symm))
  exact ⟨hfinite, hdetConv, hdetL1⟩

end LPPDifferentiability
