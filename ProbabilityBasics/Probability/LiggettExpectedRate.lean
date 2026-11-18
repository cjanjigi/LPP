/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Analysis.PositiveSubadditiveRate
public import ProbabilityBasics.Frozen.Foundations.Liggett.LiggettRowLaws
public import ProbabilityBasics.Frozen.Foundations.Liggett.LiggettSubadditive
public import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Liggett's finite expected rate

The expected-value step (2.1) of Liggett (1985), from (1.3), (1.7), and the
whole-column equality in law (1.8) of that paper. All indices in the
conclusion have positive length; diagonal entries of the supplied array are
unused. No pointwise or L1 convergence is asserted.
-/

public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace LPPDifferentiability

open ProbabilityBasics.Liggett

/-- Adjacent whole-column laws propagate to every origin. The coordinates
are all positive lengths, indexed by `k + 1`. -/
theorem liggett_column_identDistrib {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (A : ℕ → ℕ → Ω → ℝ)
    (hmeas : ∀ n : ℕ, 0 < n → Measurable (A 0 n))
    (hadj : LiggettRowLaws μ A)
    (m : ℕ) :
    IdentDistrib (fun ω (k : ℕ) => A m (m + (k + 1)) ω)
      (fun ω (k : ℕ) => A 0 (k + 1) ω) μ μ := by
  induction m with
  | zero =>
    simpa only [Nat.zero_add] using
      (IdentDistrib.refl (show AEMeasurable (fun ω (k : ℕ) => A 0 (k + 1) ω) μ from
        (measurable_pi_iff.mpr (fun k => hmeas (k + 1) (by omega))).aemeasurable))
  | succ m ih => exact (hadj m).trans ih

/-- Evaluation of the joint law gives each positive block law. -/
theorem liggett_block_identDistrib {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (A : ℕ → ℕ → Ω → ℝ)
    (hmeas : ∀ n : ℕ, 0 < n → Measurable (A 0 n))
    (hadj : LiggettRowLaws μ A)
    (m n : ℕ) (hn : 0 < n) :
    IdentDistrib (A m (m + n)) (A 0 n) μ μ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact (liggett_column_identDistrib A hmeas hadj m).comp (measurable_pi_apply k)

/-- Moment and joint law hypotheses give integrability and equality
of expectations for translated positive blocks. -/
theorem liggett_block_integrable_integral {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (A : ℕ → ℕ → Ω → ℝ)
    (hmeas : ∀ n : ℕ, 0 < n → Measurable (A 0 n))
    (hint : ∀ n : ℕ, 0 < n → Integrable (A 0 n) μ)
    (hadj : LiggettRowLaws μ A)
    (m n : ℕ) (hn : 0 < n) :
    Integrable (A m (m + n)) μ ∧
      (∫ ω, A m (m + n) ω ∂μ) = ∫ ω, A 0 n ω ∂μ := by
  have hlaw := liggett_block_identDistrib A hmeas hadj m n hn
  exact ⟨hlaw.integrable_iff.mpr (hint n hn), hlaw.integral_eq⟩

/-- Integrating origin subadditivity, after deriving the translated block
moments from the joint laws, gives positive subadditivity of origin means. -/
theorem liggett_expected_subadditive {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (A : ℕ → ℕ → Ω → ℝ)
    (hmeas : ∀ n : ℕ, 0 < n → Measurable (A 0 n))
    (hint : ∀ n : ℕ, 0 < n → Integrable (A 0 n) μ)
    (hsub : LiggettSubadditive μ A)
    (hadj : LiggettRowLaws μ A)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    (∫ ω, A 0 (m + n) ω ∂μ) ≤
      (∫ ω, A 0 m ω ∂μ) + ∫ ω, A 0 n ω ∂μ := by
  obtain ⟨hblock, heq⟩ := liggett_block_integrable_integral A hmeas hint hadj m n hn
  calc
    _ ≤ ∫ ω, (A 0 m ω + A m (m + n) ω) ∂μ :=
      integral_mono_ae (hint (m + n) (by omega)) ((hint m hm).add hblock)
        (hsub m (m + n) hm (by omega))
    _ = _ := by rw [integral_add (hint m hm) hblock, heq]

/-- Liggett (1985), (2.1): one finite real expected rate, with its limit and infimum
characterizations. The common lower bound is (1.3) of that paper; adjacent joint
column laws are (1.8), and origin subadditivity is (1.7). -/
theorem exists_liggett_expected_rate {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (A : ℕ → ℕ → Ω → ℝ)
    (hmeas : ∀ n : ℕ, 0 < n → Measurable (A 0 n))
    (hint : ∀ n : ℕ, 0 < n → Integrable (A 0 n) μ)
    (c : ℝ)
    (hlower : ∀ n : ℕ, 0 < n → -(c * (n : ℝ)) ≤ ∫ ω, A 0 n ω ∂μ)
    (hsub : LiggettSubadditive μ A)
    (hadj : LiggettRowLaws μ A) :
    ∃ γ : ℝ,
      Tendsto (fun n : ℕ => (∫ ω, A 0 (n + 1) ω ∂μ) / ((n + 1 : ℕ) : ℝ))
        atTop (𝓝 γ) ∧
      γ = sInf (range (fun n : ℕ =>
        (∫ ω, A 0 (n + 1) ω ∂μ) / ((n + 1 : ℕ) : ℝ))) := by
  apply exists_positive_subadditive_rate (fun n => ∫ ω, A 0 n ω ∂μ)
    (liggett_expected_subadditive A hmeas hint hsub hadj) (-c)
  intro n hn
  simpa only [neg_mul] using hlower n hn

end LPPDifferentiability
