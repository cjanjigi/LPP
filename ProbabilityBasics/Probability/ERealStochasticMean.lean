/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.StochasticMean
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Integrable representatives of stochastically bounded extended variables

The negative part is clipped while it still has its genuine extended value.
Monotone convergence proves finiteness before a real representative is used.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LPPDifferentiability

private theorem lintegral_le_of_strict_tails
    {Ω Λ : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ]
    {μ : Measure Ω} {ν : Measure Λ} {N : Ω → ℝ≥0∞} {f : Λ → ℝ}
    (hN : Measurable N) (hf : AEMeasurable f ν) (hf0 : 0 ≤ᵐ[ν] f)
    (htail : ∀ t : ℝ, 0 < t → μ {w | ENNReal.ofReal t < N w} ≤ ν {w | t < f w}) :
    (∫⁻ w, N w ∂μ) ≤ ∫⁻ w, ENNReal.ofReal (f w) ∂ν := by
  have hclip (n : ℕ) : (∫⁻ w, min (N w) (n : ℝ≥0∞) ∂μ) ≤
      ∫⁻ w, ENNReal.ofReal (f w) ∂ν := by
    have hn (w : Ω) : min (N w) (n : ℝ≥0∞) ≠ ∞ :=
      ne_top_of_le_ne_top (by simp) (min_le_right _ _)
    have hc : Measurable (fun w => (min (N w) (n : ℝ≥0∞)).toReal) :=
      (hN.min measurable_const).ennreal_toReal
    have hfinite : (∫⁻ w, min (N w) (n : ℝ≥0∞) ∂μ) =
        ∫⁻ w, ENNReal.ofReal ((min (N w) (n : ℝ≥0∞)).toReal) ∂μ := by
      apply lintegral_congr
      intro w
      exact (ENNReal.ofReal_toReal (hn w)).symm
    rw [hfinite, lintegral_eq_lintegral_meas_lt μ
      (Eventually.of_forall (fun w => ENNReal.toReal_nonneg)) hc.aemeasurable,
      lintegral_eq_lintegral_meas_lt ν hf0 hf]
    apply setLIntegral_mono' measurableSet_Ioi
    intro t ht
    calc
      μ {w | t < (min (N w) (n : ℝ≥0∞)).toReal} ≤
          μ {w | ENNReal.ofReal t < N w} := by
        apply measure_mono
        intro w hw
        exact lt_of_lt_of_le
          ((ENNReal.ofReal_lt_iff_lt_toReal ht.le (hn w)).mpr hw) (min_le_left _ _)
      _ ≤ ν {w | t < f w} := htail t ht
  have hsup (w : Ω) : (⨆ n : ℕ, min (N w) (n : ℝ≥0∞)) = N w := by
    rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
  calc
    (∫⁻ w, N w ∂μ) = ∫⁻ w, ⨆ n : ℕ, min (N w) (n : ℝ≥0∞) ∂μ := by
      simp only [hsup]
    _ = ⨆ n : ℕ, ∫⁻ w, min (N w) (n : ℝ≥0∞) ∂μ :=
      lintegral_iSup (fun n => hN.min measurable_const)
        (fun n m hnm w => min_le_min_left _ (by exact_mod_cast hnm))
    _ ≤ ∫⁻ w, ENNReal.ofReal (f w) ∂ν := iSup_le hclip

private theorem ofReal_lt_negativePart_iff (z : EReal) {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal t < (-z).toENNReal ↔ z < ((-t : ℝ) : EReal) := by
  induction z <;> simp [ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.le, EReal.toENNReal, ← EReal.coe_neg, EReal.bot_lt_coe, lt_neg]

/-- A real integrable upper bound and stochastic lower bound force an extended
variable to be finite almost everywhere and give one integrable representative
whose expectation dominates the stochastic lower bound. -/
theorem exists_integrable_real_of_closed_upper_tails
    {Ω Λ : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ]
    {μ : Measure Ω} {ν : Measure Λ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : Ω → EReal} {Y : Λ → ℝ} {U : Ω → ℝ}
    (hX : Measurable X) (hY : Integrable Y ν) (hU : Integrable U μ)
    (hupper : ∀ᵐ w ∂μ, X w ≤ (U w : EReal))
    (htail : ∀ a : ℝ, ν {w | a ≤ Y w} ≤ μ {w | (a : EReal) ≤ X w}) :
    (∀ᵐ w ∂μ, X w ≠ ⊥ ∧ X w ≠ ⊤) ∧
      ∃ x : Ω → ℝ, Measurable x ∧ Integrable x μ ∧
        (∀ᵐ w ∂μ, (x w : EReal) = X w) ∧ (∫ w, Y w ∂ν) ≤ ∫ w, x w ∂μ := by
  have hlower (a : ℝ) : μ {w | X w < (a : EReal)} ≤ ν {w | Y w < a} := by
    have cx : {w | X w < (a : EReal)} = {w | (a : EReal) ≤ X w}ᶜ := by ext w; simp
    have cy : {w | Y w < a} = {w | a ≤ Y w}ᶜ := by ext w; simp
    rw [cx, cy, measure_compl (measurableSet_le measurable_const hX) (measure_ne_top _ _),
      measure_compl₀ (nullMeasurableSet_le aemeasurable_const hY.aemeasurable)
        (measure_ne_top _ _)]
    simpa only [measure_univ] using tsub_le_tsub_left (htail a) 1
  have hN : Measurable (fun w => (-X w).toENNReal) := hX.neg.ereal_toENNReal
  have hnegative : (∫⁻ w, (-X w).toENNReal ∂μ) ≤
      ∫⁻ w, ENNReal.ofReal (-Y w) ∂ν := by
    have h := lintegral_le_of_strict_tails (μ := μ) (f := fun w => max (-Y w) 0) hN (hY.aemeasurable.neg.max aemeasurable_const)
      (Eventually.of_forall (fun w => le_max_right (-Y w) 0)) ?_
    · simpa only [ENNReal.ofReal_max, ENNReal.ofReal_zero,
        max_eq_left (zero_le : (0 : ℝ≥0∞) ≤ _)] using h
    · intro t ht
      have he : {w | ENNReal.ofReal t < (-X w).toENNReal} =
          {w | X w < ((-t : ℝ) : EReal)} := by
        ext w
        exact ofReal_lt_negativePart_iff (X w) ht
      have hy : {w | t < max (-Y w) 0} = {w | Y w < -t} := by
        ext w
        simp only [mem_ofPred_eq, lt_max_iff, or_iff_left (not_lt.mpr ht.le)]
        exact lt_neg
      rw [he, hy]
      exact hlower (-t)
  have hNfinite : (∫⁻ w, (-X w).toENNReal ∂μ) ≠ ∞ :=
    ne_top_of_le_ne_top hY.neg.lintegral_lt_top.ne hnegative
  have hfinite : ∀ᵐ w ∂μ, X w ≠ ⊥ ∧ X w ≠ ⊤ := by
    filter_upwards [ae_lt_top hN hNfinite, hupper] with w hw hu
    constructor
    · have hn : -X w ≠ ⊤ := EReal.toENNReal_ne_top_iff.mp hw.ne
      simpa using hn
    · intro h
      simp [h] at hu
  have hreal : ∀ᵐ w ∂μ, ((X w).toReal : EReal) = X w := by
    filter_upwards [hfinite] with w hw
    exact EReal.coe_toReal hw.2 hw.1
  have hnegint : Integrable (fun w => ((-X w).toENNReal).toReal) μ :=
    integrable_toReal_of_lintegral_ne_top hN.aemeasurable hNfinite
  have hxint : Integrable (fun w => (X w).toReal) μ := by
    apply (hU.abs.add hnegint).mono' hX.ereal_toReal.aestronglyMeasurable
    filter_upwards [hreal, hupper] with w hw hu
    have hxu : (X w).toReal ≤ U w := by
      rw [← hw] at hu
      exact EReal.coe_le_coe_iff.mp hu
    have hn : ((-X w).toENNReal).toReal = max (-(X w).toReal) 0 := by
      rw [← hw]
      simp [ENNReal.toReal_ofReal']
    change |(X w).toReal| ≤ |U w| + ((-X w).toENNReal).toReal
    rw [hn]
    rcases le_total 0 (X w).toReal with hx | hx
    · rw [abs_of_nonneg hx]
      exact hxu.trans ((le_abs_self _).trans (le_add_of_nonneg_right (le_max_right _ _)))
    · rw [abs_of_nonpos hx, max_eq_left (neg_nonneg.mpr hx)]
      exact le_add_of_nonneg_left (abs_nonneg _)
  refine ⟨hfinite, (fun w => (X w).toReal), hX.ereal_toReal, hxint, hreal, ?_⟩
  apply integral_le_of_closed_upper_tails hxint hY
  intro a
  calc
    ν {w | a ≤ Y w} ≤ μ {w | (a : EReal) ≤ X w} := htail a
    _ = μ {w | a ≤ (X w).toReal} := by
      apply measure_congr
      filter_upwards [hreal] with w hw
      apply propext
      rw [← hw, EReal.coe_le_coe_iff, EReal.toReal_coe]

end LPPDifferentiability
