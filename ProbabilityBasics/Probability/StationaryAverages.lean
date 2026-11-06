/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.SequenceAverages
public import ProbabilityBasics.Probability.BirkhoffL1
public import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Averages of a stationary sequence on its original experiment

The local sequence law is exactly the pushforward of the supplied sequence.
Every input to Birkhoff is proved from its stationary joint law and first
moment. This fills the canonical-law step in Liggett (1985), equation (2.6).
-/

public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace LPPDifferentiability

/-- Actual averages of a stationary real sequence converge almost surely and
in L1 on the original experiment. One integrable witness has mean `E B₀`;
all finite-average integrabilities are also produced. -/
theorem exists_stationary_sequence_average {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B : Ω → ℕ → ℝ)
    (hstat : IdentDistrib (fun ω => sequenceShift (B ω)) B μ μ)
    (hi : Integrable (fun ω => B ω 0) μ) :
    ∃ U : Ω → ℝ, Integrable U μ ∧
      (∀ n : ℕ, Integrable (fun ω =>
        birkhoffAverage ℝ sequenceShift (fun z : ℕ → ℝ => z 0) n (B ω)) μ) ∧
      (∀ᵐ ω ∂μ, Tendsto (fun n : ℕ =>
        birkhoffAverage ℝ sequenceShift (fun z : ℕ → ℝ => z 0) n (B ω))
        atTop (𝓝 (U ω))) ∧
      (∫ ω, U ω ∂μ) = ∫ ω, B ω 0 ∂μ ∧
      Tendsto (fun n : ℕ => ∫ ω,
        |birkhoffAverage ℝ sequenceShift (fun z : ℕ → ℝ => z 0) n (B ω) - U ω| ∂μ)
        atTop (𝓝 0) := by
  have hB : AEMeasurable B μ := hstat.aemeasurable_snd
  let κ : ProbabilityMeasure (ℕ → ℝ) :=
    ⟨μ.map B, (Measure.isProbabilityMeasure_map_iff hB).2 inferInstance⟩
  have hshift : MeasurePreserving sequenceShift (κ : Measure (ℕ → ℝ))
      (κ : Measure (ℕ → ℝ)) := by
    refine ⟨continuous_sequenceShift.measurable, ?_⟩
    change (μ.map B).map sequenceShift = μ.map B
    exact (AEMeasurable.map_map_of_aemeasurable
      continuous_sequenceShift.measurable.aemeasurable hB).trans hstat.map_eq
  have hcoord : Integrable (fun z : ℕ → ℝ => z 0) (κ : Measure (ℕ → ℝ)) :=
    (integrable_map_measure (measurable_pi_apply 0).aestronglyMeasurable hB).2 hi
  obtain ⟨g, hgm, hgi, hconv, _hinv, hmean, hL1⟩ :=
    exists_birkhoffL1 hshift (measurable_pi_apply 0) hcoord
  have hU : Integrable (fun ω => g (B ω)) μ :=
    (integrable_map_measure hgm.aestronglyMeasurable hB).1 hgi
  have hint (n : ℕ) : Integrable (fun ω =>
      birkhoffAverage ℝ sequenceShift (fun z : ℕ → ℝ => z 0) n (B ω)) μ := by
    have hn := integrable_birkhoffAverage hshift hcoord n
    exact (integrable_map_measure hn.aestronglyMeasurable hB).1 hn
  refine ⟨fun ω => g (B ω), hU, hint, ae_of_ae_map hB hconv, ?_, ?_⟩
  · calc
      (∫ ω, g (B ω) ∂μ) = ∫ z, g z ∂(κ : Measure (ℕ → ℝ)) :=
        (integral_map hB hgm.aestronglyMeasurable).symm
      _ = ∫ z : ℕ → ℝ, z 0 ∂(κ : Measure (ℕ → ℝ)) := hmean
      _ = ∫ ω, B ω 0 ∂μ := integral_map hB (measurable_pi_apply 0).aestronglyMeasurable
  · have heq (n : ℕ) :
        (∫ z, |birkhoffAverage ℝ sequenceShift (fun x : ℕ → ℝ => x 0) n z - g z|
          ∂(κ : Measure (ℕ → ℝ))) =
        ∫ ω, |birkhoffAverage ℝ sequenceShift (fun z : ℕ → ℝ => z 0) n (B ω) - g (B ω)|
          ∂μ := by
      have hierr := ((integrable_birkhoffAverage hshift hcoord n).sub hgi).abs
      exact integral_map hB hierr.aestronglyMeasurable
    exact hL1.congr' (Eventually.of_forall heq)

/-- A sequence with stationary tail and an arbitrary integrable initial value
has the same almost-sure and L1 average limit as its tail. The mean is the
mean of the first tail value; the initial value need not have that law. -/
theorem exists_tail_stationary_sequence_average {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (C : Ω → ℕ → ℝ)
    (hstat : IdentDistrib (fun ω => sequenceShift (sequenceShift (C ω)))
      (fun ω => sequenceShift (C ω)) μ μ)
    (h0 : Integrable (fun ω => C ω 0) μ)
    (h1 : Integrable (fun ω => C ω 1) μ) :
    ∃ U : Ω → ℝ, Integrable U μ ∧
      (∀ n : ℕ, Integrable (fun ω =>
        birkhoffAverage ℝ sequenceShift (fun z : ℕ → ℝ => z 0) n (C ω)) μ) ∧
      (∀ᵐ ω ∂μ, Tendsto (fun n : ℕ =>
        birkhoffAverage ℝ sequenceShift (fun z : ℕ → ℝ => z 0) n (C ω))
        atTop (𝓝 (U ω))) ∧
      (∫ ω, U ω ∂μ) = ∫ ω, C ω 1 ∂μ ∧
      Tendsto (fun n : ℕ => ∫ ω,
        |birkhoffAverage ℝ sequenceShift (fun z : ℕ → ℝ => z 0) n (C ω) - U ω| ∂μ)
        atTop (𝓝 0) := by
  obtain ⟨U, hU, hintail, hconv, hmean, hL1⟩ :=
    exists_stationary_sequence_average μ (fun ω => sequenceShift (C ω)) hstat h1
  let a (n : ℕ) (ω : Ω) :=
    birkhoffAverage ℝ sequenceShift (fun z : ℕ → ℝ => z 0) n (sequenceShift (C ω))
  let b (n : ℕ) (ω : Ω) :=
    birkhoffAverage ℝ sequenceShift (fun z : ℕ → ℝ => z 0) n (C ω)
  have hformula (n : ℕ) (ω : Ω) :
      b (n + 1) ω = (n : ℝ) / (n + 1 : ℝ) * a n ω + C ω 0 / (n + 1 : ℝ) :=
    birkhoffAverage_sequenceShift_succ (C ω) n
  have hint (n : ℕ) : Integrable (b n) μ := by
    cases n with
    | zero =>
      simpa only [b, birkhoffAverage_zero, Pi.zero_apply] using
        (integrable_const (0 : ℝ) : Integrable (fun _ : Ω => (0 : ℝ)) μ)
    | succ n =>
      have hh := ((hintail n).const_mul ((n : ℝ) / (n + 1 : ℝ))).add
        (h0.div_const (n + 1 : ℝ))
      exact hh.congr (Eventually.of_forall (fun ω => (hformula n ω).symm))
  have hcoeff : Tendsto (fun n : ℕ => (n : ℝ) / (n + 1 : ℝ)) atTop (𝓝 1) :=
    tendsto_natCast_div_add_atTop (1 : ℝ)
  have hsmall (c : ℝ) :
      Tendsto (fun n : ℕ => c / (n + 1 : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, one_mul, mul_zero] using
      (tendsto_const_nhds (x := c)).mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hfullconv : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => b n ω) atTop (𝓝 (U ω)) := by
    filter_upwards [hconv] with ω hω
    apply (tendsto_add_atTop_iff_nat 1).1
    have hh : Tendsto (fun n : ℕ =>
        (n : ℝ) / (n + 1 : ℝ) * a n ω + C ω 0 / (n + 1 : ℝ)) atTop (𝓝 (U ω)) := by
      simpa only [one_mul, add_zero] using (hcoeff.mul hω).add (hsmall (C ω 0))
    exact hh.congr' (Eventually.of_forall (fun n => (hformula n ω).symm))
  have herror (n : ℕ) (ω : Ω) :
      b (n + 1) ω - U ω =
        (n : ℝ) / (n + 1 : ℝ) * (a n ω - U ω) +
          (C ω 0 - U ω) / (n + 1 : ℝ) := by
    rw [hformula]
    have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
    field_simp [hn1]
    ring
  have hbound (n : ℕ) :
      (∫ ω, |b (n + 1) ω - U ω| ∂μ) ≤
        (∫ ω, |a n ω - U ω| ∂μ) + (∫ ω, |C ω 0 - U ω| ∂μ) / (n + 1 : ℝ) := by
    have ht : Integrable (fun ω => |a n ω - U ω|) μ := ((hintail n).sub hU).abs
    have hp : Integrable (fun ω => |C ω 0 - U ω|) μ := (h0.sub hU).abs
    calc
      (∫ ω, |b (n + 1) ω - U ω| ∂μ) ≤
          ∫ ω, (|a n ω - U ω| + |C ω 0 - U ω| / (n + 1 : ℝ)) ∂μ := by
        apply integral_mono ((hint (n + 1)).sub hU).abs
          (ht.add (hp.div_const (n + 1 : ℝ)))
        intro ω
        change |b (n + 1) ω - U ω| ≤ |a n ω - U ω| + |C ω 0 - U ω| / (n + 1 : ℝ)
        rw [herror]
        calc
          |(n : ℝ) / (n + 1 : ℝ) * (a n ω - U ω) +
              (C ω 0 - U ω) / (n + 1 : ℝ)| ≤
              |(n : ℝ) / (n + 1 : ℝ) * (a n ω - U ω)| +
                |(C ω 0 - U ω) / (n + 1 : ℝ)| := abs_add_le _ _
          _ ≤ |a n ω - U ω| + |C ω 0 - U ω| / (n + 1 : ℝ) := by
            rw [abs_mul,
              abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) / (n + 1 : ℝ)),
              abs_div, abs_of_pos (by positivity : (0 : ℝ) < n + 1)]
            have hc : (n : ℝ) / (n + 1 : ℝ) ≤ 1 :=
              (div_le_one (by positivity : (0 : ℝ) < n + 1)).2
                (le_add_of_nonneg_right zero_le_one)
            exact add_le_add (mul_le_of_le_one_left (abs_nonneg (a n ω - U ω)) hc) le_rfl
      _ = (∫ ω, |a n ω - U ω| ∂μ) +
          (∫ ω, |C ω 0 - U ω| ∂μ) / (n + 1 : ℝ) := by
        rw [integral_add ht (hp.div_const _), integral_div]
  have hfullL1 : Tendsto (fun n : ℕ => ∫ ω, |b n ω - U ω| ∂μ) atTop (𝓝 0) := by
    apply (tendsto_add_atTop_iff_nat 1).1
    have hz := hL1.add (hsmall (∫ ω, |C ω 0 - U ω| ∂μ))
    have hz' : Tendsto (fun n : ℕ =>
        (∫ ω, |a n ω - U ω| ∂μ) + (∫ ω, |C ω 0 - U ω| ∂μ) / (n + 1 : ℝ))
        atTop (𝓝 0) := by simpa only [zero_add] using hz
    exact squeeze_zero (fun n => integral_nonneg fun ω => abs_nonneg _) hbound hz'
  exact ⟨U, hU, hint, hfullconv, hmean, hfullL1⟩

end LPPDifferentiability
