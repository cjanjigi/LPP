/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.LatticeUniformDeviation
public import LPP_Foundations.Probability.PassageMeanBounds
public import Martin2004.Probability.RealExpectedTruncation

import Martin2004.Probability.BoundedPassageConcentration
import Mathlib.Tactic

/-!
# Bounded passage fluctuations

Martin (2004), Lemma 5.3 gives eventual linear-error control of centered
passage times for bounded weights. The same estimate is transferred to the
coordinatewise clipped field on the original environment space.
-/

public section

open MeasureTheory

namespace LPPDifferentiability

/-- Clipping any probability environment before taking a finite passage
maximum gives a genuinely integrable random variable on the original space.
No moment or support condition on the original marginal is needed. -/
theorem integrable_clipped_lastPassage_of_probability
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (L : ℝ) (hL : 0 ≤ L)
    (d : ℕ × ℕ) :
    Integrable
      (fun ω : Environment =>
        lastPassage (fun z => max (-L) (min L (ω z))) 0 d)
      (environmentLaw μ) := by
  let clipEnv : Environment → Environment := fun ω z => max (-L) (min L (ω z))
  have hclipEnv : Measurable clipEnv :=
    measurable_coordinatewise_environment_map
      (fun x : ℝ => max (-L) (min L x)) (by fun_prop)
  have hbound : ∀ᵐ x ∂μ.map (fun x : ℝ => max (-L) (min L x)), |x| ≤ L :=
    ae_abs_le_map_clipping μ L hL
  have hboundedPassage :
      Integrable (fun ω : Environment => lastPassage ω 0 d)
        (environmentLaw (μ.map (fun x : ℝ => max (-L) (min L x)))) :=
    integrable_lastPassage_of_ae_abs_le
      (μ.map (fun x : ℝ => max (-L) (min L x))) L hbound 0 d
  have hmapPassage :
      Integrable (fun ω : Environment => lastPassage ω 0 d)
        ((environmentLaw μ).map clipEnv) := by
    rw [environmentLaw_map_clipped μ L]
    exact hboundedPassage
  change Integrable
    (fun ω : Environment => lastPassage (clipEnv ω) 0 d)
    (environmentLaw μ)
  exact hmapPassage.comp_measurable hclipEnv

/-- Almost-sure events for the clipped canonical environment pull back to
its literal coordinatewise clipped field on the original environment. -/
private theorem ae_of_ae_clipped_environment_map
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (L : ℝ)
    (P : Environment → Prop)
    (hP : ∀ᵐ ω ∂environmentLaw
      (μ.map (fun x : ℝ => max (-L) (min L x))), P ω) :
    ∀ᵐ ω ∂environmentLaw μ,
      P (fun z => max (-L) (min L (ω z))) := by
  let clipEnv : Environment → Environment := fun ω z => max (-L) (min L (ω z))
  have hclipEnv : Measurable clipEnv :=
    measurable_coordinatewise_environment_map
      (fun x : ℝ => max (-L) (min L x)) (by fun_prop)
  have hmap : ∀ᵐ ω ∂(environmentLaw μ).map clipEnv, P ω := by
    rw [environmentLaw_map_clipped μ L]
    exact hP
  simpa only [clipEnv] using ae_of_ae_map hclipEnv.aemeasurable hmap

/-- The centered eventual-deviation event for a clipped marginal transfers to
the actual clipped field on the original environment. The integral identity
keeps the center equal to the genuine original-space clipped mean. -/
private theorem ae_eventually_clipped_centered_deviation_of_mapped_law
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (L : ℝ)
    (hP : ∀ᵐ ω ∂environmentLaw
      (μ.map (fun x : ℝ => max (-L) (min L x))),
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
          |lastPassage ω 0 d -
            ∫ η : Environment, lastPassage η 0 d
              ∂environmentLaw (μ.map (fun x : ℝ => max (-L) (min L x)))| <
            ε * ((d.1 + d.2 : ℕ) : ℝ)) :
    ∀ᵐ ω ∂environmentLaw μ,
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
          |lastPassage (fun z => max (-L) (min L (ω z))) 0 d -
            ∫ η : Environment,
              lastPassage (fun z => max (-L) (min L (η z))) 0 d
                ∂environmentLaw μ| <
            ε * ((d.1 + d.2 : ℕ) : ℝ) := by
  have hpull := ae_of_ae_clipped_environment_map μ L _ hP
  filter_upwards [hpull] with ω hω
  intro ε hε
  obtain ⟨N, hN, hdeviation⟩ := hω ε hε
  refine ⟨N, hN, ?_⟩
  intro d hd
  have h := hdeviation d hd
  rw [integral_lastPassage_map_clipping μ L d] at h
  exact h

/-- With positive cutoff and displacement length, substituting
`u = epsilon * n` turns Martin's actual tail into one exponential envelope.
This is only scalar normalization; it is not a passage concentration result. -/
private theorem exp_scaled_length_identity
    (ε L n : ℝ) (hL : 0 < L) (hn : 0 < n) :
    Real.exp (64 - (ε * n) ^ 2 / (64 * n * L ^ 2)) =
      Real.exp 64 * Real.exp (-(ε ^ 2 / (64 * L ^ 2) * n)) := by
  have hn0 : n ≠ 0 := ne_of_gt hn
  have hL0 : L ≠ 0 := ne_of_gt hL
  have hscale : (ε * n) ^ 2 / (64 * n * L ^ 2) =
      (ε ^ 2 / (64 * L ^ 2)) * n := by
    field_simp [hn0, hL0]
  rw [hscale, Real.exp_sub, div_eq_mul_inv, ← Real.exp_neg]

private theorem exp_scaled_length_rate_pos
    (ε L : ℝ) (hε : 0 < ε) (hL : 0 < L) :
    0 < ε ^ 2 / (64 * L ^ 2) := by
  positivity

/-- Under a bounded marginal law, the actual last-passage value is eventually
within every positive linear error tolerance of its genuine canonical mean,
on one event that works for all tolerances. -/
public theorem ae_eventually_lastPassage_centered_uniform_deviation_of_ae_abs_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (L : ℝ) (hL : 0 < L)
    (hbound : ∀ᵐ x ∂μ, |x| ≤ L) :
    ∀ᵐ ω ∂environmentLaw μ,
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
          |lastPassage ω 0 d -
            ∫ η : Environment, lastPassage η 0 d ∂environmentLaw μ| <
            ε * ((d.1 + d.2 : ℕ) : ℝ) := by
  let D : Environment → ℕ × ℕ → ℝ := fun ω d =>
    lastPassage ω 0 d -
      ∫ η : Environment, lastPassage η 0 d ∂environmentLaw μ
  have hTail : ∀ ε : ℝ, 0 < ε →
      ∃ K c : ℝ, 0 ≤ K ∧ 0 < c ∧
        ∀ d : ℕ × ℕ, d ≠ (0, 0) →
          (environmentLaw μ).real
              {ω | ε * ((d.1 + d.2 : ℕ) : ℝ) ≤ |D ω d|} ≤
            K * Real.exp (-c * ((d.1 + d.2 : ℕ) : ℝ)) := by
    intro ε hε
    let K : ℝ := Real.exp 64
    let c : ℝ := ε ^ 2 / (64 * L ^ 2)
    have hK : 0 ≤ K := by positivity
    have hc : 0 < c := exp_scaled_length_rate_pos ε L hε hL
    refine ⟨K, c, hK, hc, ?_⟩
    intro d hd
    have hlength : 0 < d.1 + d.2 := by
      by_contra h
      have hzero : d.1 + d.2 = 0 := by omega
      have hfirst : d.1 = 0 := by omega
      have hsecond : d.2 = 0 := by omega
      apply hd
      exact Prod.ext hfirst hsecond
    let n : ℝ := ((d.1 + d.2 : ℕ) : ℝ)
    have hn : 0 < n := by
      dsimp [n]
      exact_mod_cast hlength
    have hu : 0 < ε * n := mul_pos hε hn
    have hactual :=
      measure_abs_lastPassage_sub_integral_ge_le_martin μ d L hL hbound
        hlength (u := ε * n) hu
    calc
      (environmentLaw μ).real {ω | ε * ((d.1 + d.2 : ℕ) : ℝ) ≤ |D ω d|} ≤
          Real.exp (64 - (ε * n) ^ 2 / (64 * n * L ^ 2)) := by
        simpa only [D, n] using hactual
      _ = K * Real.exp (-c * n) := by
        simpa only [K, c, neg_mul] using
          (exp_scaled_length_identity ε L n hL hn)
  have hdeviation :=
    ae_eventually_lattice_relative_deviation_of_exp_tail
      (environmentLaw μ) D hTail
  filter_upwards [hdeviation] with ω hω
  intro ε hε
  obtain ⟨N, hN, hdev⟩ := hω ε hε
  refine ⟨N, hN, ?_⟩
  intro d hd
  simpa only [D] using hdev d hd

/-- For every original probability law, its literal clipped passage field has
the same common almost-sure centered deviation bound, with its genuine mean
integral on the original environment space. No moment or support condition on
the original marginal is required. -/
public theorem ae_eventually_clipped_lastPassage_centered_uniform_deviation
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (L : ℝ) (hL : 0 < L) :
    ∀ᵐ ω ∂environmentLaw μ,
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
          |lastPassage (fun z => max (-L) (min L (ω z))) 0 d -
            ∫ η : Environment,
              lastPassage (fun z => max (-L) (min L (η z))) 0 d
                ∂environmentLaw μ| <
            ε * ((d.1 + d.2 : ℕ) : ℝ) := by
  have hbound :
      ∀ᵐ x ∂μ.map (fun x : ℝ => max (-L) (min L x)), |x| ≤ L :=
    ae_abs_le_map_clipping μ L hL.le
  have hdeviation :=
    ae_eventually_lastPassage_centered_uniform_deviation_of_ae_abs_le
      (μ.map (fun x : ℝ => max (-L) (min L x))) L hL hbound
  exact ae_eventually_clipped_centered_deviation_of_mapped_law μ L hdeviation

end LPPDifferentiability

end
