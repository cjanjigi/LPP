/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Frozen.Foundations.Liggett.LiggettBlockStationary
public import ProbabilityBasics.Probability.LiggettLimitMoments
public import ProbabilityBasics.Probability.LiggettLowerComparison
public import ProbabilityBasics.Probability.LiggettBlockUpper
public import ProbabilityBasics.Probability.L1MovingMajorant
import ProbabilityBasics.Probability.LiggettBlockAverages
import ProbabilityBasics.Probability.LiggettBlockDecomposition
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Tactic.Ring

/-! # Liggett's joint almost-sure and L1 convergence theorem

Liggett's hypotheses produce one integrable limit on the original space and one
common finite expected rate. The ergodic specialization is in a separate file.
-/

public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators

namespace LPPDifferentiability

open ProbabilityBasics.Liggett

/-- Liggett's hypotheses give one measurable integrable limit on the original space,
almost-sure and L1 convergence, and one common rate for the mean, equal to the
expected-rate limit and to the infimum over positive lengths. -/
theorem exists_liggett_convergence {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : ℕ → ℕ → Ω → ℝ)
    (hm : ∀ n : ℕ, 0 < n → Measurable (A 0 n))
    (hi : ∀ n : ℕ, 0 < n → Integrable (A 0 n) μ)
    (c : ℝ)
    (hlower : ∀ n : ℕ, 0 < n → -(c * (n : ℝ)) ≤ ∫ ω, A 0 n ω ∂μ)
    (hsub : LiggettSubadditive μ A)
    (hadj : LiggettRowLaws μ A)
    (hstat : LiggettBlockStationary μ A) :
    ∃ γ : ℝ, ∃ g : Ω → ℝ, Measurable g ∧ Integrable g μ ∧
      (∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => A 0 (n + 1) ω / ((n + 1 : ℕ) : ℝ))
        atTop (𝓝 (g ω))) ∧
      (∫ ω, g ω ∂μ) = γ ∧
      Tendsto (fun n : ℕ => (∫ ω, A 0 (n + 1) ω ∂μ) / ((n + 1 : ℕ) : ℝ))
        atTop (𝓝 γ) ∧
      γ = sInf (range (fun n : ℕ =>
        (∫ ω, A 0 (n + 1) ω ∂μ) / ((n + 1 : ℕ) : ℝ))) ∧
      Tendsto (fun n : ℕ => ∫ ω,
        |A 0 (n + 1) ω / ((n + 1 : ℕ) : ℝ) - g ω| ∂μ) atTop (𝓝 0) := by
  obtain ⟨γ, κ, Y, hγ, hγinf, _hYm, hYi, hYmean, htail⟩ :=
    exists_liggett_lower_comparison μ A hm hi c hlower hsub hadj
  let f : ℕ → Ω → ℝ := fun n ω => A 0 (n + 1) ω / ((n + 1 : ℕ) : ℝ)
  let L : Ω → EReal := fun ω => liminf (fun n => (f n ω : EReal)) atTop
  let H : Ω → EReal := fun ω => limsup (fun n => (f n ω : EReal)) atTop
  have hLm : Measurable L :=
    Measurable.liminf fun n => ((hm (n + 1) (by omega)).div_const _).coe_real_ereal
  have hHm : Measurable H :=
    Measurable.limsup fun n => ((hm (n + 1) (by omega)).div_const _).coe_real_ereal
  have hLH (ω : Ω) : L ω ≤ H ω := liminf_le_limsup
  obtain ⟨U, hUi, _hUmean, hUupper⟩ :=
    exists_liggett_limsup_upper A hm hi hsub hadj 1 (by omega) (hstat 1 (by omega))
  have hLupper : ∀ᵐ ω ∂μ, L ω ≤ (U ω : EReal) := by
    filter_upwards [hUupper] with ω hω
    exact (hLH ω).trans hω
  have htailL (a : ℝ) : (κ : Measure (ℕ → ℝ)) {z | a ≤ Y z} ≤
      μ {ω | (a : EReal) ≤ L ω} := by
    simpa only [L, f, Nat.cast_add, Nat.cast_one] using htail a
  obtain ⟨_hLfinite, l, hlm, hli, hlreal, hlmean⟩ :=
    exists_integrable_real_of_closed_upper_tails hLm hYi hUi hLupper htailL
  have hlH : ∀ᵐ ω ∂μ, (l ω : EReal) ≤ H ω := by
    filter_upwards [hlreal] with ω hω
    exact hω.trans_le (hLH ω)
  obtain ⟨_hHfinite, u, _hum, hui, hureal, hbetween⟩ :=
    exists_integrable_real_of_ereal_sandwich hHm hli hUi hlH hUupper
  have humean : (∫ ω, u ω ∂μ) ≤ γ := by
    rw [hγinf]
    apply le_csInf (range_nonempty _)
    rintro _ ⟨n, rfl⟩
    obtain ⟨V, hVi, hVmean, hVupper⟩ :=
      exists_liggett_limsup_upper A hm hi hsub hadj (n + 1) (by omega)
        (hstat (n + 1) (by omega))
    calc
      (∫ ω, u ω ∂μ) ≤ ∫ ω, V ω ∂μ := by
        apply integral_mono_ae hui hVi
        filter_upwards [hureal, hVupper] with ω hr hv
        change H ω ≤ (V ω : EReal) at hv
        rw [← hr] at hv
        exact EReal.coe_le_coe_iff.mp hv
      _ = _ := hVmean
  have hlu : l ≤ᵐ[μ] u := hbetween.mono fun _ hω => hω.1
  obtain ⟨hleq, hlγ, _huγ⟩ := ae_eq_and_integral_eq_of_integral_sandwich
    hli hui hlu (hYmean.trans hlmean) humean
  have hconv : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (l ω)) := by
    filter_upwards [hlreal, hureal, hleq] with ω hl hu heq
    apply EReal.tendsto_coe.mp
    apply tendsto_of_liminf_eq_limsup hl.symm
    exact hu.symm.trans (congrArg (fun x : ℝ => (x : EReal)) heq.symm)
  have hfi (n : ℕ) : Integrable (f n) μ := (hi (n + 1) (by omega)).div_const _
  obtain ⟨B, hBi, hBqi, _hBconv, _hBmean, hBL1⟩ :=
    exists_liggett_block_average (μ := μ) A hm hi hadj 1 (by omega)
      (hstat 1 (by omega))
  let Bq : ℕ → Ω → ℝ := fun q ω =>
    (∑ i ∈ Finset.range q, A (i * 1) ((i + 1) * 1) ω) / (q : ℝ)
  have hmean : Tendsto (fun n => ∫ ω, f n ω ∂μ) atTop (𝓝 (∫ ω, l ω ∂μ)) := by
    simpa only [f, integral_div, hlγ] using hγ
  have hdom (n : ℕ) : ∀ᵐ ω ∂μ,
      |max (f n ω - l ω) 0| ≤ |Bq (n + 1) ω - l ω| := by
    filter_upwards [liggett_origin_block_bound_ae A hsub 1 (n + 1)
      (by omega) (by omega)] with ω hω
    have hbound : f n ω ≤ Bq (n + 1) ω := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      simpa only [Nat.mul_one] using hω
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le ((sub_le_sub_right hbound _).trans (le_abs_self _)) (abs_nonneg _)
  have hcancel (n : ℕ) (ω : Ω) :
      (Bq (n + 1) ω - l ω) - (B ω - l ω) = Bq (n + 1) ω - B ω := by ring
  have hgconv : Tendsto (fun n => ∫ ω,
      |(Bq (n + 1) ω - l ω) - (B ω - l ω)| ∂μ) atTop (𝓝 0) := by
    simpa only [hcancel, Bq, Function.comp_def] using
      hBL1.comp (tendsto_add_atTop_nat 1)
  have hL1 := tendsto_integral_abs_sub_of_ae_tendsto_of_pos_l1_majorant
    hfi hli (fun n => (hBqi (n + 1)).sub hli) (hBi.sub hli)
      hconv hmean hdom hgconv
  exact ⟨γ, l, hlm, hli, hconv, hlγ, hγ, hγinf, hL1⟩

end LPPDifferentiability
