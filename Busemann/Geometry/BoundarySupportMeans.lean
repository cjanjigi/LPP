/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Frozen.Definitions.SupportTilt
public import Martin2004.Shape.ExpectedRateShape
import Busemann.Geometry.SupportIdentities
import Busemann.Frozen.Geometry.LeftExtremeTiltExistsUnique
import LPP_Foundations.Analysis.AbsoluteMomentShape
import LPP_Foundations.Analysis.AbsoluteMomentAxes
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! The support/contact squeeze for the longitudinal boundary means in
GRS arXiv:1510.00860v1, Lemma 5.1. No boundary mean limit is assumed. -/

@[expose] public section
open LPPDifferentiability MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace LPP.Busemann

private theorem coefficient_tendsto_of_contact
    (u v a b G : ℕ → ℝ) (m : ℝ)
    (hu : ∀ n, 0 < u n) (hv : ∀ n, 0 ≤ v n)
    (ha : ∀ n, m ≤ a n) (hb : ∀ n, m ≤ b n)
    (hcontact : ∀ n, G n = a n * u n + b n * v n)
    (hU : Tendsto u atTop (𝓝 1)) (hV : Tendsto v atTop (𝓝 0))
    (hG : Tendsto G atTop (𝓝 m)) : Tendsto a atTop (𝓝 m) := by
  have hUpper (n : ℕ) : a n ≤ (G n - m * v n) / u n := by
    apply (le_div_iff₀ (hu n)).mpr
    have hterm := mul_le_mul_of_nonneg_right (hb n) (hv n)
    linarith only [hcontact n, hterm]
  have hUpperLimit : Tendsto (fun n => (G n - m * v n) / u n) atTop (𝓝 m) := by
    have hFun : (fun n => (G n - m * v n) / u n) = (fun n => G n - m * v n) / u := by
      funext n
      rw [Pi.div_apply]
    rw [hFun]
    simpa only [mul_zero, sub_zero, div_one] using
      (hG.sub (tendsto_const_nhds.mul hV)).div hU one_ne_zero
  exact tendsto_const_nhds.squeeze hUpperLimit ha hUpper

/-- Actual supported tilts have longitudinal means approaching the marginal
mean at either unit axis. The support majorant and contact, shape axis values
and continuity prove the mean step of GRS arXiv:1510.00860v1, Lemma 5.1. -/
theorem supported_longitudinal_means_tendsto_axes
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    (g : Quadrant → ℝ) (hg : IsExpectedRateShape μ g)
    (ξs : ℕ → InteriorDirection) (hs : ℕ → SupportTilt g)
    (hSupport : ∀ n, SupportsAt g (ξs n) (hs n).1) :
    (Tendsto (fun n => (ξs n).1) atTop (𝓝 ((1, 0) : Quadrant)) →
      Tendsto (fun n => -(hs n).1.1) atTop (𝓝 (∫ t : ℝ, t ∂μ))) ∧
    (Tendsto (fun n => (ξs n).1) atTop (𝓝 ((0, 1) : Quadrant)) →
      Tendsto (fun n => -(hs n).1.2) atTop (𝓝 (∫ t : ℝ, t ∂μ))) := by
  obtain ⟨hcont, hhom, _⟩ := expected_rate_shape_geometry_of_absolute_moment μ g hmoment hg
  obtain ⟨_, hAxisE, hAxisN⟩ :=
    expected_rate_shape_axes_and_symmetry_of_absolute_moment μ hmoment g hg
  let m : ℝ := ∫ t : ℝ, t ∂μ
  have hAxisE' : g (1, 0) = m := by simpa only [NNReal.coe_one, mul_one] using hAxisE 1
  have hAxisN' : g (0, 1) = m := by simpa only [NNReal.coe_one, mul_one] using hAxisN 1
  have hData (n : ℕ) :
      m ≤ -(hs n).1.1 ∧ m ≤ -(hs n).1.2 ∧
      g (ξs n).1 = -(hs n).1.1 * ((ξs n).1.1 : ℝ) +
        -(hs n).1.2 * ((ξs n).1.2 : ℝ) := by
    have hd := (supportsAt_iff_through_origin_majorant_and_contact
      g (ξs n) (hs n).1 hhom).mp (hSupport n)
    refine ⟨?_, ?_, hd.2⟩
    · simpa only [hAxisE', NNReal.coe_one, NNReal.coe_zero, mul_one, mul_zero, add_zero]
        using hd.1 (1, 0)
    · simpa only [hAxisN', NNReal.coe_one, NNReal.coe_zero, mul_one, mul_zero, zero_add]
        using hd.1 (0, 1)
  constructor
  · intro hξ
    apply coefficient_tendsto_of_contact
      (fun n => ((ξs n).1.1 : ℝ)) (fun n => ((ξs n).1.2 : ℝ))
      (fun n => -(hs n).1.1) (fun n => -(hs n).1.2) (fun n => g (ξs n).1) m
      (fun n => by exact_mod_cast (ξs n).2.1) (fun n => (ξs n).1.2.2)
      (fun n => (hData n).1) (fun n => (hData n).2.1) (fun n => (hData n).2.2)
    · exact NNReal.tendsto_coe.mpr hξ.fst_nhds
    · exact NNReal.tendsto_coe.mpr hξ.snd_nhds
    · simpa only [Function.comp_def, hAxisE'] using hcont.continuousAt.tendsto.comp hξ
  · intro hξ
    apply coefficient_tendsto_of_contact
      (fun n => ((ξs n).1.2 : ℝ)) (fun n => ((ξs n).1.1 : ℝ))
      (fun n => -(hs n).1.2) (fun n => -(hs n).1.1) (fun n => g (ξs n).1) m
      (fun n => by exact_mod_cast (ξs n).2.2.1) (fun n => (ξs n).1.1.2)
      (fun n => (hData n).2.1) (fun n => (hData n).1)
      (fun n => by rw [(hData n).2.2, add_comm])
    · exact NNReal.tendsto_coe.mpr hξ.snd_nhds
    · exact NNReal.tendsto_coe.mpr hξ.fst_nhds
    · simpa only [Function.comp_def, hAxisN'] using hcont.continuousAt.tendsto.comp hξ

/-- Countably many ordered actual interior contacts approach both axes.
Their longitudinal support means converge by the proved contact squeeze,
not by an extra boundary convergence premise. -/
theorem exists_ordered_boundary_contacts
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    (g : Quadrant → ℝ) (hg : IsExpectedRateShape μ g) :
    ∃ (ξE ξN : ℕ → InteriorDirection) (hE hN : ℕ → SupportTilt g),
      StrictMono (fun n => ((ξE n).1.1 : ℝ)) ∧
      StrictAnti (fun n => ((ξN n).1.1 : ℝ)) ∧
      (∀ n, SupportsAt g (ξE n) (hE n).1 ∧ SupportsAt g (ξN n) (hN n).1) ∧
      Tendsto (fun n => (ξE n).1) atTop (𝓝 ((1, 0) : Quadrant)) ∧
      Tendsto (fun n => (ξN n).1) atTop (𝓝 ((0, 1) : Quadrant)) ∧
      Tendsto (fun n => -(hE n).1.1) atTop (𝓝 (∫ t : ℝ, t ∂μ)) ∧
      Tendsto (fun n => -(hN n).1.2) atTop (𝓝 (∫ t : ℝ, t ∂μ)) := by
  classical
  let a (n : ℕ) : ℝ≥0 := ((n : ℝ≥0) + 1) / ((n : ℝ≥0) + 2)
  let b (n : ℕ) : ℝ≥0 := 1 / ((n : ℝ≥0) + 2)
  have hSum (n : ℕ) : (a n : ℝ) + (b n : ℝ) = 1 := by
    dsimp only [a, b]
    push_cast
    have hne : (n : ℝ) + 2 ≠ 0 := by positivity
    field_simp [hne]
    ring
  let ξE (n : ℕ) : InteriorDirection :=
    ⟨(a n, b n), by exact ⟨by dsimp [a]; positivity, by dsimp [b]; positivity, hSum n⟩⟩
  let ξN (n : ℕ) : InteriorDirection :=
    ⟨(b n, a n), by exact ⟨by dsimp [b]; positivity, by dsimp [a]; positivity,
      by simpa only [add_comm] using hSum n⟩⟩
  have hALimit : Tendsto a atTop (𝓝 1) := by
    simpa only [a, Function.comp_def, Nat.cast_add, Nat.cast_one, add_assoc,
      one_add_one_eq_two] using
      (tendsto_natCast_div_add_atTop (1 : ℝ≥0)).comp (tendsto_add_atTop_nat 1)
  have hBLimit : Tendsto b atTop (𝓝 0) := by
    simpa only [b, Function.comp_def, Nat.cast_add, Nat.cast_one, add_assoc,
      one_add_one_eq_two] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ≥0)).comp (tendsto_add_atTop_nat 1)
  have hELimit : Tendsto (fun n => (ξE n).1) atTop (𝓝 ((1, 0) : Quadrant)) :=
    hALimit.prodMk_nhds hBLimit
  have hNLimit : Tendsto (fun n => (ξN n).1) atTop (𝓝 ((0, 1) : Quadrant)) :=
    hBLimit.prodMk_nhds hALimit
  obtain ⟨_, hhom, hconc⟩ := expected_rate_shape_geometry_of_absolute_moment μ g hmoment hg
  have hContact (ξ : InteriorDirection) : ∃ h : SupportTilt g, SupportsAt g ξ h.1 := by
    obtain ⟨h, hh⟩ := (exists_unique_left_extreme_tilt g hconc hhom ξ).exists
    exact ⟨h, hh.1⟩
  choose hE hhE using fun n => hContact (ξE n)
  choose hN hhN using fun n => hContact (ξN n)
  refine ⟨ξE, ξN, hE, hN, ?_, ?_, fun n => ⟨hhE n, hhN n⟩,
    hELimit, hNLimit,
    (supported_longitudinal_means_tendsto_axes μ hmoment g hg ξE hE hhE).1 hELimit,
    (supported_longitudinal_means_tendsto_axes μ hmoment g hg ξN hN hhN).2 hNLimit⟩
  · intro n k hnk
    change (a n : ℝ) < (a k : ℝ)
    dsimp only [a]
    push_cast
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
    have hc : (n : ℝ) < (k : ℝ) := by exact_mod_cast hnk
    nlinarith only [hc]
  · intro n k hnk
    change (b k : ℝ) < (b n : ℝ)
    dsimp only [b]
    push_cast
    apply one_div_lt_one_div_of_lt (by positivity)
    have hc : (n : ℝ) < k := by exact_mod_cast hnk
    linarith only [hc]

end LPP.Busemann
