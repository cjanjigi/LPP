/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.MartinWeakContinuity
public import Martin2004.Probability.BoundedExpectedUniform
public import Martin2004.Probability.BoundedPassageFluctuations
public import Martin2004.Probability.UniformPassageUpper
public import LPP_Foundations.Probability.TruncationTails
public import LPP_Foundations.Model.LastPassage.Truncation

import Mathlib.Tactic

/-!
# One-sided uniform sample upper approximation

The positive half of Lemma 5.2 of Martin (2004), followed by Lemmas 5.3 to 5.5,
needs a first moment and only the positive integrated square-root tail. All
clipped rates are identified by their mapped floor expectation limits.
-/

public section

open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

namespace LPPDifferentiability

private theorem ae_eventually_lastPassage_upper_fixed_tolerance
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞)
    (g : Quadrant → ℝ)
    (hg : ∀ x : Quadrant, Tendsto (fun n : ℕ =>
      (∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
        ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (g x)))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᵐ ω ∂environmentLaw μ, ∃ N : ℕ, 1 ≤ N ∧
      ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        lastPassage ω 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0)) <
          ε * ((d.1 + d.2 : ℕ) : ℝ) := by
  let δ : ℝ := ε / 8
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  obtain ⟨C, _hC, hupper⟩ := exists_uniform_lastPassage_eventually_upper_bound
  have htail : Tendsto (fun L : ℝ =>
      C * (∫⁻ t in Ioi L, (μ (Ioi t)) ^ (1 / 2 : ℝ)).toReal)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_martin_positive_tail_toReal_zero μ hpos).const_mul C
  obtain ⟨Lp, hLp⟩ := eventually_atTop.1 (htail.eventually_lt_const hδ)
  obtain ⟨Lr, _hLr, hrate⟩ :=
    exists_clipped_real_expected_rate_relative_approximation μ hμ hpos g hg δ hδ
  let L : ℝ := max 1 (max Lp Lr)
  have hL1 : 1 ≤ L := le_max_left _ _
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hLpL : Lp ≤ L := (le_max_left _ _).trans (le_max_right _ _)
  have hLrL : Lr ≤ L := (le_max_right _ _).trans (le_max_right _ _)
  have hsmall := hLp L hLpL
  obtain ⟨r, _hrc, hrlim, _hroriginal, hrerror⟩ := hrate L hLrL
  have hclipbound : ∀ᵐ t ∂μ.map (fun t : ℝ => max (-L) (min L t)), |t| ≤ L :=
    ae_abs_le_map_clipping μ L hL.le
  obtain ⟨b, hb, _hbunique⟩ :=
    exists_unique_uniform_lastPassage_real_expected_rate_of_ae_abs_le
      (μ.map (fun t : ℝ => max (-L) (min L t))) L hL.le hclipbound
  have hbr : b = r := by
    funext x
    exact tendsto_nhds_unique (hb.1.1.1.1 x) (hrlim x)
  obtain ⟨Nm, _hNm, hmean⟩ := hb.2.2 δ hδ
  have hpositiveFinite :
      (∫⁻ t in Ioi (0 : ℝ),
        ((μ.map (fun x : ℝ => max (x - L) 0)) (Ioi t)) ^ (1 / 2 : ℝ)) < ∞ := by
    rw [positive_remainder_sqrt_tail]
    exact lt_of_le_of_lt (lintegral_mono_set (Ioi_subset_Ioi hL.le)) hpos
  have hp := hupper (μ.map (fun x : ℝ => max (x - L) 0)) hpositiveFinite
  have hpmap : MeasurePreserving
      (fun ω : Environment => fun z : Lattice => max (ω z - L) 0)
      (environmentLaw μ) (environmentLaw (μ.map (fun x : ℝ => max (x - L) 0))) :=
    ⟨measurable_coordinatewise_environment_map (fun x : ℝ => max (x - L) 0)
      (by fun_prop), environmentLaw_map_positive_remainder μ L⟩
  have hpback := hpmap.quasiMeasurePreserving.ae hp
  have hc := ae_eventually_clipped_lastPassage_centered_uniform_deviation μ L hL
  filter_upwards [hpback, hc] with ω hωp hωc
  obtain ⟨Np, hNp, hrem⟩ := hωp δ hδ
  obtain ⟨Nc, _hNc, hcenter⟩ := hωc δ hδ
  refine ⟨max Np (max Nc Nm), hNp.trans (le_max_left _ _), ?_⟩
  intro d hd
  have hdp : Np ≤ d.1 + d.2 := (le_max_left _ _).trans hd
  have hdc : Nc ≤ d.1 + d.2 :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hd)
  have hdm : Nm ≤ d.1 + d.2 :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hd)
  have hlength : (0 : ℝ) < ((d.1 + d.2 : ℕ) : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < Np) hdp)
  have hremd := hrem (d.1 + d.2) hdp d le_rfl
  rw [positive_remainder_sqrt_tail] at hremd
  have hremSmall := mul_lt_mul_of_pos_left hsmall hlength
  have hcenterd := (abs_lt.mp (hcenter d hdc)).2
  have hmeand := (abs_lt.mp (hmean d hdm)).2
  rw [integral_lastPassage_map_clipping μ L d, hbr] at hmeand
  have hrated := (abs_le.mp (hrerror ((d.1 : ℝ≥0), (d.2 : ℝ≥0)))).1
  have hcast : ((d.1 : ℝ≥0) : ℝ) + ((d.2 : ℝ≥0) : ℝ) =
      ((d.1 + d.2 : ℕ) : ℝ) := by simp only [NNReal.coe_natCast, Nat.cast_add]
  rw [hcast] at hrated
  have hfinite := lastPassage_le_clipped_add_positive_remainder ω 0 d L hL.le
  dsimp only [δ] at hsmall hremd hremSmall hcenterd hmeand hrated
  nlinarith only [hfinite, hremd, hremSmall, hcenterd, hmeand, hrated, hlength, hε]

/-- On one event, every positive real tolerance bounds the upper sample error
uniformly over all sufficiently long natural endpoints. The same g is fixed
by the full floor-integral limits. Signed, atomic and degenerate laws are
allowed, and no negative square-root tail is required. -/
theorem ae_eventually_lastPassage_uniform_upper_of_integrable_and_positive_tail
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞)
    (g : Quadrant → ℝ)
    (hg : ∀ x : Quadrant, Tendsto (fun n : ℕ =>
      (∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
        ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (g x))) :
    ∀ᵐ ω ∂environmentLaw μ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        lastPassage ω 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0)) ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ) := by
  have heach (k : ℕ) :=
    ae_eventually_lastPassage_upper_fixed_tolerance μ hμ hpos g hg
      (1 / ((k : ℝ) + 1)) (by positivity)
  have hall := ae_all_iff.mpr heach
  filter_upwards [hall] with ω hω
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨N, hN, hbound⟩ := hω k
  refine ⟨N, hN, ?_⟩
  intro d hd
  exact (hbound d hd).le.trans
    (mul_le_mul_of_nonneg_right hk.le (Nat.cast_nonneg _))

end LPPDifferentiability
