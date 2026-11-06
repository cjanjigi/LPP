/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.LastPassage.Truncation
public import LPP_Foundations.Probability.TruncationTails
public import Martin2004.Probability.UniformPassageUpper

/-!
# Uniform approximation by clipped passage times

The finite comparison uses both clipping inequalities. It does not identify the
difference of two passage maxima with a difference along one common path.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace LPPDifferentiability

/-- The two finite clipping comparisons control the absolute difference. -/
theorem lastPassage_sub_clipped_abs_le_remainders (ω : Environment) (u : Lattice)
    (d : ℕ × ℕ) (L : ℝ) (hL : 0 ≤ L) :
    |lastPassage ω u d - lastPassage (fun z => max (-L) (min L (ω z))) u d| ≤
      lastPassage (fun z => max (ω z - L) 0) u d +
        lastPassage (fun z => max (-ω z - L) 0) u d := by
  have hp := lastPassage_le_clipped_add_positive_remainder ω u d L hL
  have hn := lastPassage_clipped_le_add_negative_remainder ω u d L hL
  have hp0 : 0 ≤ lastPassage (fun z => max (ω z - L) 0) u d := by
    simpa only [mul_zero] using
      const_le_lastPassage (fun z => max (ω z - L) 0) u d 0
        (fun _ => le_max_right _ _)
  have hn0 : 0 ≤ lastPassage (fun z => max (-ω z - L) 0) u d := by
    simpa only [mul_zero] using
      const_le_lastPassage (fun z => max (-ω z - L) 0) u d 0
        (fun _ => le_max_right _ _)
  exact abs_le.mpr ⟨by linarith only [hn, hp0], by linarith only [hp, hn0]⟩

/-- The positive remainder has finite integrated square-root tail for a nonnegative cutoff. -/
theorem positive_remainder_sqrt_tail_lt_top (μ : Measure ℝ)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞)
    (L : ℝ) (hL : 0 ≤ L) :
    (∫⁻ t in Ioi (0 : ℝ),
      ((μ.map (fun x : ℝ => max (x - L) 0)) (Ioi t)) ^ (1 / 2 : ℝ)) < ∞ := by
  rw [positive_remainder_sqrt_tail]
  exact lt_of_le_of_lt (lintegral_mono_set (Ioi_subset_Ioi hL)) hpos

/-- The closed negative tail controls finiteness, including marginal atoms. -/
theorem negative_remainder_sqrt_tail_lt_top (μ : Measure ℝ)
    (hneg : (∫⁻ t in Iio (0 : ℝ), (μ (Iic t)) ^ (1 / 2 : ℝ)) < ∞)
    (L : ℝ) (hL : 0 ≤ L) :
    (∫⁻ t in Ioi (0 : ℝ),
      ((μ.map (fun x : ℝ => max (-x - L) 0)) (Ioi t)) ^ (1 / 2 : ℝ)) < ∞ := by
  apply lt_of_le_of_lt (negative_remainder_sqrt_tail_le μ L)
  exact lt_of_le_of_lt (lintegral_mono_set (Iio_subset_Iio (by linarith only [hL]))) hneg

/-- Both real-valued remainder tail constants become small beyond one deterministic cutoff. -/
theorem exists_remainder_sqrt_tail_cutoff (μ : Measure ℝ)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞)
    (hneg : (∫⁻ t in Iio (0 : ℝ), (μ (Iic t)) ^ (1 / 2 : ℝ)) < ∞)
    (C ε : ℝ) (hε : 0 < ε) :
    ∃ L0 : ℝ, 0 ≤ L0 ∧ ∀ L ≥ L0,
      C * (∫⁻ t in Ioi (0 : ℝ),
        ((μ.map (fun x : ℝ => max (x - L) 0)) (Ioi t)) ^ (1 / 2 : ℝ)).toReal < ε ∧
      C * (∫⁻ t in Ioi (0 : ℝ),
        ((μ.map (fun x : ℝ => max (-x - L) 0)) (Ioi t)) ^ (1 / 2 : ℝ)).toReal < ε := by
  have hp := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    (tendsto_positive_remainder_sqrt_tail_zero μ hpos)
  have hn := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    (tendsto_negative_remainder_sqrt_tail_zero μ hneg)
  have hp' : Tendsto (fun L : ℝ => C * (∫⁻ t in Ioi (0 : ℝ),
      ((μ.map (fun x : ℝ => max (x - L) 0)) (Ioi t)) ^ (1 / 2 : ℝ)).toReal)
      atTop (𝓝 0) := by simpa only [Function.comp_apply, ENNReal.toReal_zero, mul_zero] using hp.const_mul C
  have hn' : Tendsto (fun L : ℝ => C * (∫⁻ t in Ioi (0 : ℝ),
      ((μ.map (fun x : ℝ => max (-x - L) 0)) (Ioi t)) ^ (1 / 2 : ℝ)).toReal)
      atTop (𝓝 0) := by simpa only [Function.comp_apply, ENNReal.toReal_zero, mul_zero] using hn.const_mul C
  have he := (hp'.eventually (gt_mem_nhds hε)).and (hn'.eventually (gt_mem_nhds hε))
  obtain ⟨L1, hL1⟩ := eventually_atTop.mp he
  exact ⟨max 0 L1, le_max_left _ _, fun L hL => hL1 L ((le_max_right _ _).trans hL)⟩

/-- Martin's two square-root tail conditions give uniform approximation by
clipped passage times. The deterministic cutoff precedes the environment,
and each fixed cutoff has its own full-measure event. -/
theorem uniform_lastPassage_clipped_approximation (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞)
    (hneg : (∫⁻ t in Iio (0 : ℝ), (μ (Iic t)) ^ (1 / 2 : ℝ)) < ∞)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ L0 : ℝ, 0 ≤ L0 ∧ ∀ L ≥ L0,
      ∀ᵐ ω ∂environmentLaw μ, ∃ N : ℕ, 1 ≤ N ∧
        ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
          |lastPassage ω 0 d - lastPassage (fun z => max (-L) (min L (ω z))) 0 d| <
            ε * ((d.1 + d.2 : ℕ) : ℝ) := by
  obtain ⟨C, _, hbound⟩ := exists_uniform_lastPassage_eventually_upper_bound
  obtain ⟨L0, hL0, hsmall⟩ := exists_remainder_sqrt_tail_cutoff μ hpos hneg C (ε / 4)
    (by linarith only [hε])
  refine ⟨L0, hL0, ?_⟩
  intro L hL
  have hLnonneg := hL0.trans hL
  have hp := hbound (μ.map (fun x : ℝ => max (x - L) 0))
    (positive_remainder_sqrt_tail_lt_top μ hpos L hLnonneg)
  have hn := hbound (μ.map (fun x : ℝ => max (-x - L) 0))
    (negative_remainder_sqrt_tail_lt_top μ hneg L hLnonneg)
  have hpmap : MeasurePreserving
      (fun ω : Environment => fun z : Lattice => max (ω z - L) 0)
      (environmentLaw μ) (environmentLaw (μ.map (fun x : ℝ => max (x - L) 0))) :=
    ⟨measurable_coordinatewise_environment_map (fun x : ℝ => max (x - L) 0)
      (by fun_prop), environmentLaw_map_positive_remainder μ L⟩
  have hnmap : MeasurePreserving
      (fun ω : Environment => fun z : Lattice => max (-ω z - L) 0)
      (environmentLaw μ) (environmentLaw (μ.map (fun x : ℝ => max (-x - L) 0))) :=
    ⟨measurable_coordinatewise_environment_map (fun x : ℝ => max (-x - L) 0)
      (by fun_prop), environmentLaw_map_negative_remainder μ L⟩
  have hpback := hpmap.quasiMeasurePreserving.ae hp
  have hnback := hnmap.quasiMeasurePreserving.ae hn
  filter_upwards [hpback, hnback] with ω hωp hωn
  obtain ⟨Np, hNp, hpb⟩ := hωp (ε / 4) (by linarith only [hε])
  obtain ⟨Nn, _, hnb⟩ := hωn (ε / 4) (by linarith only [hε])
  refine ⟨max Np Nn, hNp.trans (le_max_left _ _), ?_⟩
  intro d hd
  have hdp := (le_max_left Np Nn).trans hd
  have hdn := (le_max_right Np Nn).trans hd
  have hlen : (0 : ℝ) < ((d.1 + d.2 : ℕ) : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < Np) hdp)
  have hpp := hpb (d.1 + d.2) hdp d le_rfl
  have hnn := hnb (d.1 + d.2) hdn d le_rfl
  obtain ⟨hpsmall, hnsmall⟩ := hsmall L hL
  calc
    |lastPassage ω 0 d - lastPassage (fun z => max (-L) (min L (ω z))) 0 d| ≤
        lastPassage (fun z => max (ω z - L) 0) 0 d +
          lastPassage (fun z => max (-ω z - L) 0) 0 d :=
      lastPassage_sub_clipped_abs_le_remainders ω 0 d L hLnonneg
    _ < ((d.1 + d.2 : ℕ) : ℝ) *
          (C * (∫⁻ t in Ioi (0 : ℝ),
            ((μ.map (fun x : ℝ => max (x - L) 0)) (Ioi t)) ^ (1 / 2 : ℝ)).toReal + ε / 4) +
        ((d.1 + d.2 : ℕ) : ℝ) *
          (C * (∫⁻ t in Ioi (0 : ℝ),
            ((μ.map (fun x : ℝ => max (-x - L) 0)) (Ioi t)) ^ (1 / 2 : ℝ)).toReal + ε / 4) :=
      add_lt_add hpp hnn
    _ = ((d.1 + d.2 : ℕ) : ℝ) *
        ((C * (∫⁻ t in Ioi (0 : ℝ),
            ((μ.map (fun x : ℝ => max (x - L) 0)) (Ioi t)) ^ (1 / 2 : ℝ)).toReal + ε / 4) +
          (C * (∫⁻ t in Ioi (0 : ℝ),
            ((μ.map (fun x : ℝ => max (-x - L) 0)) (Ioi t)) ^ (1 / 2 : ℝ)).toReal + ε / 4)) :=
      (mul_add _ _ _).symm
    _ < ((d.1 + d.2 : ℕ) : ℝ) * ε :=
      mul_lt_mul_of_pos_left (by linarith only [hpsmall, hnsmall]) hlen
    _ = ε * ((d.1 + d.2 : ℕ) : ℝ) := mul_comm _ _

end LPPDifferentiability
