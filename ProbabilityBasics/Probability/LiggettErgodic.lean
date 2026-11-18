/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.LiggettConvergence
public import ProbabilityBasics.Probability.ErgodicBlockAverages
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Order.LiminfLimsup

/-! # Liggett's ergodic specialization

The final clause of Theorem 1.10 of Liggett (1985) follows the final sentence
of the proof of (2.2). Ergodicity concerns every positive-length tail block law,
without a common array shift assumption.
-/

public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators

namespace LPPDifferentiability

open ProbabilityBasics.Liggett

/-- If all positive-length stationary block processes are ergodic,
Liggett's normalized array converges almost surely and in L1 to the same
finite real rate characterized by the expected-rate limit and positive infimum. -/
theorem exists_liggett_ergodic_convergence {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : ℕ → ℕ → Ω → ℝ)
    (hmeas : ∀ n : ℕ, 0 < n → Measurable (A 0 n))
    (hint : ∀ n : ℕ, 0 < n → Integrable (A 0 n) μ)
    (c : ℝ)
    (hlower : ∀ n : ℕ, 0 < n → -(c * (n : ℝ)) ≤ ∫ ω, A 0 n ω ∂μ)
    (hsub : LiggettSubadditive μ A)
    (hadj : LiggettRowLaws μ A)
    (hstat : LiggettBlockStationary μ A)
    (hErg : ∀ k : ℕ, 0 < k → Ergodic sequenceShift
      (μ.map (fun ω (j : ℕ) => A ((j + 1) * k) ((j + 2) * k) ω))) :
    ∃ γ : ℝ,
      Tendsto (fun n : ℕ => (∫ ω, A 0 (n + 1) ω ∂μ) / ((n + 1 : ℕ) : ℝ))
        atTop (𝓝 γ) ∧
      γ = sInf (range (fun n : ℕ =>
        (∫ ω, A 0 (n + 1) ω ∂μ) / ((n + 1 : ℕ) : ℝ))) ∧
      (∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => A 0 (n + 1) ω / ((n + 1 : ℕ) : ℝ))
        atTop (𝓝 γ)) ∧
      Tendsto (fun n : ℕ => ∫ ω,
        |A 0 (n + 1) ω / ((n + 1 : ℕ) : ℝ) - γ| ∂μ) atTop (𝓝 0) := by
  obtain ⟨γ, g, _hgm, hgi, hconv, hmean, hγ, hγinf, hL1⟩ :=
    exists_liggett_convergence μ A hmeas hint c hlower hsub hadj hstat
  have hupper : ∀ᵐ ω ∂μ, ∀ k : ℕ,
      limsup (fun n : ℕ =>
        ((A 0 (n + 1) ω / ((n + 1 : ℕ) : ℝ) : ℝ) : EReal)) atTop ≤
      (((∫ ω, A 0 (k + 1) ω ∂μ) / ((k + 1 : ℕ) : ℝ) : ℝ) : EReal) := by
    apply ae_all_iff.mpr
    intro k
    have havg := (ae_tendsto_liggett_block_average_of_ergodic A hmeas hint hadj
      (k + 1) (Nat.zero_lt_succ _) (hstat (k + 1) (Nat.zero_lt_succ _))
        (hErg (k + 1) (Nat.zero_lt_succ _))).2.1
    exact ae_liggett_limsup_le_of_block_average A hmeas hint hsub hadj
      (k + 1) (Nat.zero_lt_succ _) (fun _ => ∫ ω, A 0 (k + 1) ω ∂μ) havg
  have hle : g ≤ᵐ[μ] (fun _ => γ) := by
    filter_upwards [hconv, hupper] with ω hω hu
    rw [hγinf]
    apply le_csInf (range_nonempty _)
    rintro _ ⟨k, rfl⟩
    have hlim := (EReal.tendsto_coe.mpr hω).limsup_eq
    exact EReal.coe_le_coe_iff.mp (hlim ▸ hu k)
  have heq : g =ᵐ[μ] (fun _ => γ) := by
    apply (integral_eq_iff_of_ae_le hgi (integrable_const γ) hle).mp
    exact hmean.trans (integral_eq_const (ae_of_all μ fun _ => rfl)).symm
  refine ⟨γ, hγ, hγinf, ?_, ?_⟩
  · filter_upwards [hconv, heq] with ω hω hg
    exact hg ▸ hω
  · have herror (n : ℕ) :
        (∫ ω, |A 0 (n + 1) ω / ((n + 1 : ℕ) : ℝ) - g ω| ∂μ) =
        ∫ ω, |A 0 (n + 1) ω / ((n + 1 : ℕ) : ℝ) - γ| ∂μ := by
      apply integral_congr_ae
      filter_upwards [heq] with ω hω
      rw [hω]
    exact hL1.congr' (Eventually.of_forall herror)

end LPPDifferentiability
