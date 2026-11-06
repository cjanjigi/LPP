/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Analysis.ExponentialShapeFormula
public import Martin2004.Model.LastPassage.Stationary
public import Martin2004.Probability.ExponentialLaw
public import LPP_Foundations.Probability.PassageIntegrable
public import LPP_Foundations.Probability.PassageLaw
public import Martin2004.Probability.StationaryMean
public import Martin2004.Shape.ExpectedRateShape

/-!
# The upper bound for the exponential shape

Martin (2004), in the proof of Theorem 2.4, states the exponential shape formula without proof.
The proof here uses the stationary model.

Let `g` be an expected-rate shape of the `Exp(1)` law. The mean of the last-passage time from the
origin equals the mean of the last-passage time from `(1, 1)` (translation). Almost surely the
latter is at most the stationary passage time of parameter `ρ`, whose mean is explicit. Dividing
by `N` and letting `N → ∞` along `⌊N x⌋` gives
`g x ≤ x₁ / (1 - ρ) + x₂ / ρ`. At `ρ = √x₂ / (√x₁ + √x₂)` the right side is `(√x₁ + √x₂)²`.
On the axes the right side is approached as `ρ → 0` or `ρ → 1`, or the known axis value of the
shape is used.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace LPPDifferentiability

/-- One grid size. For `0 < ρ < 1`, the mean of the passage time from the origin to
`(m, n)` under i.i.d. `Exp(1)` weights is at most the mean `1 + (m + 1) / (1 - ρ) + (n + 1) / ρ`
of the stationary passage time to `(m + 1, n + 1)`. -/
theorem integral_lastPassage_le_stationary {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (m n : ℕ) :
    ∫ ω : Environment, lastPassage ω 0 (m, n) ∂environmentLaw (expMeasure 1) ≤
      1 + ((m : ℝ) + 1) / (1 - ρ) + ((n : ℝ) + 1) / ρ := by
  have hμ := (integrable_and_integral_id_expMeasure one_pos).1
  have htrans : ∫ ω : Environment, lastPassage ω ((1, 1) + 0) (m, n)
      ∂environmentLaw (expMeasure 1) =
      ∫ ω : Environment, lastPassage ω 0 (m, n) ∂environmentLaw (expMeasure 1) :=
    integral_lastPassage_translation (expMeasure 1) hμ (1, 1) 0 (m, n)
  rw [add_zero] at htrans
  obtain ⟨hGint, hGmean⟩ := integrable_and_integral_stationaryPassage hρ0 hρ1 (m + 1) (n + 1)
  have hle : ∫ ω : Environment, lastPassage ω (1, 1) (m, n) ∂environmentLaw (expMeasure 1) ≤
      ∫ ω : Environment, stationaryPassage ρ ω (m + 1) (n + 1)
        ∂environmentLaw (expMeasure 1) := by
    refine integral_mono_ae (integrable_lastPassage (expMeasure 1) hμ (1, 1) (m, n)) hGint ?_
    filter_upwards [ae_nonneg_environmentLaw_expMeasure_one] with ω hω
    exact lastPassage_le_stationaryPassage hρ0 hρ1 hω m n
  rw [htrans, hGmean] at hle
  simpa using hle

/-- The stationary model bounds every expected-rate shape of the `Exp(1)` law: for every
parameter `0 < ρ < 1`, `g x ≤ x₁ / (1 - ρ) + x₂ / ρ`. The proof divides the grid bound
`integral_lastPassage_le_stationary` at `(⌊N x₁⌋, ⌊N x₂⌋)` by `N` and lets `N → ∞`. -/
theorem le_stationaryRate_of_isExpectedRateShape {g : Quadrant → ℝ}
    (hg : IsExpectedRateShape (expMeasure 1) g) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (x : Quadrant) :
    g x ≤ (x.1 : ℝ) / (1 - ρ) + (x.2 : ℝ) / ρ := by
  have hρ1' : 0 < 1 - ρ := sub_pos.2 hρ1
  set C : ℝ := 1 + 1 / (1 - ρ) + 1 / ρ with hC
  set L : ℝ := (x.1 : ℝ) / (1 - ρ) + (x.2 : ℝ) / ρ with hL
  have hb : Tendsto (fun N : ℕ => L + C * (1 / (N : ℝ))) atTop (𝓝 L) := by
    simpa using
      (tendsto_const_nhds (x := L)).add
        (tendsto_const_nhds (x := C) |>.mul tendsto_one_div_atTop_nhds_zero_nat)
  refine le_of_tendsto_of_tendsto (hg x) hb ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hm : ((⌊(N : ℝ) * (x.1 : ℝ)⌋₊ : ℕ) : ℝ) ≤ (N : ℝ) * (x.1 : ℝ) :=
    Nat.floor_le (mul_nonneg hNpos.le x.1.2)
  have hn : ((⌊(N : ℝ) * (x.2 : ℝ)⌋₊ : ℕ) : ℝ) ≤ (N : ℝ) * (x.2 : ℝ) :=
    Nat.floor_le (mul_nonneg hNpos.le x.2.2)
  have hgrid := integral_lastPassage_le_stationary hρ0 hρ1 ⌊(N : ℝ) * (x.1 : ℝ)⌋₊
    ⌊(N : ℝ) * (x.2 : ℝ)⌋₊
  rw [div_le_iff₀ hNpos]
  have hm' : (((⌊(N : ℝ) * (x.1 : ℝ)⌋₊ : ℕ) : ℝ) + 1) / (1 - ρ) ≤
      ((N : ℝ) * (x.1 : ℝ) + 1) / (1 - ρ) :=
    div_le_div_of_nonneg_right (by linarith) hρ1'.le
  have hn' : (((⌊(N : ℝ) * (x.2 : ℝ)⌋₊ : ℕ) : ℝ) + 1) / ρ ≤
      ((N : ℝ) * (x.2 : ℝ) + 1) / ρ :=
    div_le_div_of_nonneg_right (by linarith) hρ0.le
  have hid : (L + C * (1 / (N : ℝ))) * N =
      1 + ((N : ℝ) * (x.1 : ℝ) + 1) / (1 - ρ) + ((N : ℝ) * (x.2 : ℝ) + 1) / ρ := by
    rw [hL, hC]
    field_simp
    ring
  rw [hid]
  linarith

/-- The exponential shape bounds every expected-rate shape of the
`Exp(1)` law on the closed quadrant: `g x ≤ (√x₁ + √x₂)²`. On the open quadrant this is the
stationary bound at `ρ = √x₂ / (√x₁ + √x₂)` (`characteristicParameter_spec`). On the vertical
axis the stationary bound `x₂ / ρ` is let to `ρ → 1`; on the horizontal axis the known axis
value `g (s, 0) = s` is used. -/
theorem le_exponentialShape_of_isExpectedRateShape {g : Quadrant → ℝ}
    (hg : IsExpectedRateShape (expMeasure 1) g) (x : Quadrant) :
    g x ≤ exponentialShape x := by
  obtain ⟨s, t⟩ := x
  rcases eq_or_ne s 0 with rfl | hs
  · -- vertical axis: `g (0, t) ≤ t / ρ` for every `ρ < 1`
    have hlim : Tendsto (fun ρ : ℝ => (((0 : ℝ≥0) : ℝ)) / (1 - ρ) + (t : ℝ) / ρ)
        (𝓝[<] 1) (𝓝 (exponentialShape (0, t))) := by
      have hcont : ContinuousAt (fun ρ : ℝ => ((0 : ℝ≥0) : ℝ) / (1 - ρ) + (t : ℝ) / ρ) 1 := by
        simp only [NNReal.coe_zero, zero_div]
        exact continuousAt_const.add (continuousAt_const.div continuousAt_id one_ne_zero)
      have hval : exponentialShape (0, t) =
          ((0 : ℝ≥0) : ℝ) / (1 - 1) + (t : ℝ) / 1 := by
        simp [exponentialShape]
      rw [hval]
      exact hcont.tendsto.mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 from one_pos)] with ρ hρ
    exact le_stationaryRate_of_isExpectedRateShape hg hρ.1 hρ.2 (0, t)
  rcases eq_or_ne t 0 with rfl | ht
  · -- horizontal axis: `g (s, 0) = s`
    obtain ⟨hmean, -, hpos⟩ := expMeasure_one_martin_hypotheses
    obtain ⟨-, haxis⟩ :=
      isExpectedRateShape_continuous_and_axis_of_integrable_and_positive_tail
        (expMeasure 1) hmean hpos hg
    rw [haxis s, (integrable_and_integral_id_expMeasure one_pos).2]
    simp [exponentialShape]
  · -- open quadrant
    obtain ⟨h0, h1, heq⟩ := characteristicParameter_spec (pos_iff_ne_zero.2 hs)
      (pos_iff_ne_zero.2 ht)
    exact heq ▸ le_stationaryRate_of_isExpectedRateShape hg h0 h1 (s, t)

end LPPDifferentiability
