/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.AnimalPositiveMean
public import LPP_Foundations.Probability.TruncationTails
public import LPP_Foundations.Probability.PassageIntegrable
public import LPP_Foundations.Model.LastPassage.Truncation
public import LPP_Foundations.Model.LastPassage.AnimalComparison

/-!
# Finite expected positive clipping error

This file bounds the positive half of the clipping error in Martin (2004), (3.12), for each
finite endpoint, before passage to a limit. The bound is a universal constant times the
integrated tail of the marginal law, and the constant comes from the positive animal mean
estimate. The statement makes no claim relating this constant to any almost-sure bound.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace LPPDifferentiability

/-- The positive remainder `max (x - L) 0` has a finite first moment under the mapped law. -/
theorem integrable_id_map_positive_remainder (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) (L : ℝ) :
    Integrable (fun x : ℝ => x) (μ.map (fun x : ℝ => max (x - L) 0)) := by
  apply (integrable_map_measure measurable_id.aestronglyMeasurable
    (show Measurable (fun x : ℝ => max (x - L) 0) by fun_prop).aemeasurable).2
  exact (hμ.sub (integrable_const L)).sup (integrable_const 0)

private theorem integrable_id_map_clipping (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) (L : ℝ) :
    Integrable (fun x : ℝ => x) (μ.map (fun x : ℝ => max (-L) (min L x))) := by
  apply (integrable_map_measure measurable_id.aestronglyMeasurable
    (show Measurable (fun x : ℝ => max (-L) (min L x)) by fun_prop).aemeasurable).2
  exact (integrable_const (-L)).sup ((integrable_const L).inf hμ)

/-- The last-passage time in the positive remainder environment is integrable, and its mean
equals the mean of the last-passage time under the mapped environment law. -/
theorem positive_remainder_lastPassage_integrable_integral (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hμ : Integrable (fun x : ℝ => x) μ)
    (L : ℝ) (d : ℕ × ℕ) :
    Integrable (fun ω : Environment =>
      lastPassage (fun z => max (ω z - L) 0) 0 d) (environmentLaw μ) ∧
    (∫ ω : Environment, lastPassage (fun z => max (ω z - L) 0) 0 d ∂environmentLaw μ) =
      ∫ ω : Environment, lastPassage ω 0 d
        ∂environmentLaw (μ.map (fun x : ℝ => max (x - L) 0)) := by
  have hm := measurable_coordinatewise_environment_map (fun x : ℝ => max (x - L) 0)
    (by fun_prop)
  have hi := integrable_lastPassage (μ.map (fun x : ℝ => max (x - L) 0))
    (integrable_id_map_positive_remainder μ hμ L) 0 d
  have hi' : Integrable (fun ω : Environment => lastPassage ω 0 d)
      ((environmentLaw μ).map (fun ω : Environment => fun z => max (ω z - L) 0)) := by
    rw [environmentLaw_map_positive_remainder]
    exact hi
  refine ⟨hi'.comp_measurable hm, ?_⟩
  have heq := integral_map hm.aemeasurable hi'.aestronglyMeasurable
  rw [environmentLaw_map_positive_remainder] at heq
  exact heq.symm

/-- A universal constant `C` bounds, for every cutoff `L ≥ 0`, the mean loss from clipping the
environment at `±L`, and the three last-passage times involved are integrable. The tails are
strict (`Ioi t`), which is the right convention also at atoms of `μ`. -/
theorem exists_expected_positive_clipping_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
      Integrable (fun x : ℝ => x) μ →
      (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞ →
      ∀ (L : ℝ), 0 ≤ L → ∀ d : ℕ × ℕ,
      Integrable (fun ω : Environment => lastPassage ω 0 d) (environmentLaw μ) ∧
      Integrable (fun ω : Environment =>
        lastPassage (fun z => max (-L) (min L (ω z))) 0 d) (environmentLaw μ) ∧
      Integrable (fun ω : Environment =>
        lastPassage (fun z => max (ω z - L) 0) 0 d) (environmentLaw μ) ∧
      (∫ ω : Environment, lastPassage ω 0 d ∂environmentLaw μ) -
        (∫ ω : Environment,
          lastPassage (fun z => max (-L) (min L (ω z))) 0 d ∂environmentLaw μ) ≤
        C * (d.1 + d.2 : ℕ) * (∫⁻ t in Ioi L, (μ (Ioi t)) ^ (1 / 2 : ℝ)).toReal := by
  obtain ⟨C, hC, hmean⟩ := exists_positive_animalMaximum_mean_bound
  refine ⟨C, hC, ?_⟩
  intro μ _ hμ hpos L hL d
  have horig := integrable_lastPassage μ hμ 0 d
  have hclipmap := integrable_lastPassage
    (μ.map (fun x : ℝ => max (-L) (min L x))) (integrable_id_map_clipping μ hμ L) 0 d
  have hclipmap' : Integrable (fun ω : Environment => lastPassage ω 0 d)
      ((environmentLaw μ).map
        (fun ω : Environment => fun z => max (-L) (min L (ω z)))) := by
    rw [environmentLaw_map_clipped]
    exact hclipmap
  have hclip : Integrable (fun ω : Environment =>
      lastPassage (fun z => max (-L) (min L (ω z))) 0 d) (environmentLaw μ) :=
    hclipmap'.comp_measurable
    (measurable_coordinatewise_environment_map (fun x : ℝ => max (-L) (min L x))
      (by fun_prop))
  obtain ⟨hrem, hremmean⟩ := positive_remainder_lastPassage_integrable_integral μ hμ L d
  refine ⟨horig, hclip, hrem, ?_⟩
  have hfinite : (∫⁻ t in Ioi L, (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞ :=
    (lintegral_mono_set (Ioi_subset_Ioi hL)).trans_lt hpos
  have hremtail :
      (∫⁻ t in Ioi (0 : ℝ),
        ((μ.map (fun x : ℝ => max (x - L) 0)) (Ioi t)) ^ (1 / 2 : ℝ)) < ∞ := by
    rw [positive_remainder_sqrt_tail]
    exact hfinite
  have hbound :
      (∫ ω : Environment, lastPassage (fun z => max (ω z - L) 0) 0 d ∂environmentLaw μ) ≤
        C * (d.1 + d.2 : ℕ) * (∫⁻ t in Ioi L, (μ (Ioi t)) ^ (1 / 2 : ℝ)).toReal := by
    by_cases hd : d.1 + d.2 = 0
    · have he : d = (0, 0) := Prod.ext (by omega) (by omega)
      subst d
      simp only [lastPassage_zero, integral_zero, Nat.add_zero, Nat.cast_zero, mul_zero, zero_mul, le_refl]
    · have hn : 1 ≤ d.1 + d.2 := by omega
      obtain ⟨ha, hb⟩ := (hmean (μ.map (fun x : ℝ => max (x - L) 0))
        (d.1 + d.2) hn).2 hremtail
      rw [hremmean]
      calc
        _ ≤ ∫ ω : Environment,
            animalMaximum (d.1 + d.2) hn (fun z => max (ω z) 0)
            ∂environmentLaw (μ.map (fun x : ℝ => max (x - L) 0)) :=
          integral_mono (integrable_lastPassage _ (integrable_id_map_positive_remainder μ hμ L) 0 d)
            ha (fun ω => lastPassage_le_animalMaximum_atOrigin ω d (by omega))
        _ ≤ _ := by rw [positive_remainder_sqrt_tail] at hb; exact hb
  have hcomp := integral_mono horig (hclip.add hrem)
    (fun ω => lastPassage_le_clipped_add_positive_remainder ω 0 d L hL)
  change (∫ ω : Environment, lastPassage ω 0 d ∂environmentLaw μ) ≤
    ∫ ω : Environment, lastPassage (fun z => max (-L) (min L (ω z))) 0 d +
      lastPassage (fun z => max (ω z - L) 0) 0 d ∂environmentLaw μ at hcomp
  rw [integral_add hclip hrem] at hcomp
  exact (sub_le_iff_le_add.mpr (by simpa only [add_comm] using hcomp)).trans hbound

end LPPDifferentiability
