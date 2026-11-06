/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.LiggettRayInputs
public import ProbabilityBasics.Probability.LiggettErgodic
public import LPP_Foundations.Probability.MartinFirstMoment
public import Martin2004.Probability.AnimalPositiveMean
public import LPP_Foundations.Model.LastPassage.AnimalComparison

/-!
# Signed last-passage limits along natural lattice rays

The proof applies Liggett (1985), Theorem 1.10, to the negated last-passage
array. Positive block sizes and the tail blocks beginning at index one are
kept unchanged. The zero direction is treated directly.
-/

public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal Pointwise

namespace LPPDifferentiability

/-- An internal application of Liggett: a finite linear expected upper bound
for actual passage values yields one deterministic finite signed ray rate.
The theorem after it derives this bound from Martin's tails. -/
theorem exists_lastPassage_ray_convergence_of_expected_bound
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) (a : ℕ × ℕ) (c : ℝ)
    (hupper : ∀ n : ℕ, 0 < n →
      (∫ ω, lastPassage ω 0 (n • a) ∂environmentLaw μ) ≤ c * (n : ℝ)) :
    ∃ g : ℝ,
      Tendsto (fun n : ℕ =>
        (∫ ω, lastPassage ω 0 (n • a) ∂environmentLaw μ) / (n : ℝ))
        atTop (𝓝 g) ∧
      g = sSup (range (fun n : ℕ =>
        (∫ ω, lastPassage ω 0 ((n + 1) • a) ∂environmentLaw μ) /
          ((n + 1 : ℕ) : ℝ))) ∧
      (∀ᵐ ω ∂environmentLaw μ, Tendsto
        (fun n : ℕ => lastPassage ω 0 (n • a) / (n : ℝ)) atTop (𝓝 g)) ∧
      Tendsto (fun n : ℕ => ∫ ω,
        |lastPassage ω 0 (n • a) / (n : ℝ) - g| ∂environmentLaw μ)
        atTop (𝓝 0) := by
  by_cases ha : a = 0
  · subst a
    have hzero (ω : Environment) : lastPassage ω 0 (0 : ℕ × ℕ) = 0 :=
      lastPassage_zero ω 0
    refine ⟨0, ?_, ?_, ?_, ?_⟩
    · simpa only [smul_zero, hzero, integral_zero, zero_div] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    · simp only [smul_zero, hzero, integral_zero, zero_div,
        range_const, csSup_singleton]
    · exact ae_of_all _ fun ω => by
        simpa only [smul_zero, hzero, zero_div] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    · simpa only [smul_zero, hzero, zero_div, sub_zero, abs_zero,
        integral_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  obtain ⟨γ, hmean, hinf, hae, hL1⟩ :=
    exists_liggett_ergodic_convergence (environmentLaw μ)
      (negLastPassageRayArray a)
      (fun n _ => measurable_negLastPassageRayArray_origin a n)
      (fun n _ => integrable_negLastPassageRayArray_origin μ hμ a n)
      c (fun n hn => by
        simpa only [negLastPassageRayArray, Nat.sub_zero, zero_smul,
          integral_neg] using neg_le_neg (hupper n hn))
      (fun m n hm hmn => ae_of_all _ fun ω =>
        negLastPassageRayArray_origin_subadditive a ω m n hm hmn)
      (negLastPassageRayArray_column_identDistrib μ a)
      (fun k _ => by
        have hshift :
            (fun ω (j : ℕ) =>
              negLastPassageRayArray a ((j + 2) * k) ((j + 3) * k) ω) =
            (fun ω => sequenceShift (fun j : ℕ =>
              negLastPassageRayArray a ((j + 1) * k) ((j + 2) * k) ω)) := by
          funext ω j
          change negLastPassageRayArray a ((j + 2) * k) ((j + 3) * k) ω =
            negLastPassageRayArray a (((j + 1) + 1) * k) (((j + 1) + 2) * k) ω
          rw [show j + 1 + 1 = j + 2 by omega,
            show j + 1 + 2 = j + 3 by omega]
        rw [hshift]
        exact negLastPassageRayArray_tailBlocks_identDistrib μ a k)
      (ergodic_negLastPassageRayArray_tailBlocks_shift μ a ha)
  refine ⟨-γ, ?_, ?_, ?_, ?_⟩
  · apply (tendsto_add_atTop_iff_nat 1).mp
    simpa only [negLastPassageRayArray, Nat.sub_zero, zero_smul, integral_neg,
      neg_div, neg_neg] using hmean.neg
  · rw [hinf, ← Real.sSup_neg]
    congr 1
    ext x
    simp only [Set.mem_neg, mem_range, negLastPassageRayArray, Nat.sub_zero,
      zero_smul, integral_neg, neg_div]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, by linarith only [hn]⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, by linarith only [hn]⟩
  · filter_upwards [hae] with ω hω
    apply (tendsto_add_atTop_iff_nat 1).mp
    simpa only [negLastPassageRayArray, Nat.sub_zero, zero_smul,
      neg_div, neg_neg] using hω.neg
  · apply (tendsto_add_atTop_iff_nat 1).mp
    have habs (x : ℝ) : |(-x) - γ| = |x - (-γ)| := by
      rw [sub_neg_eq_add, ← abs_neg]
      congr 1
      ring
    simpa only [negLastPassageRayArray, Nat.sub_zero, zero_smul, neg_div,
      habs] using hL1

/-- Martin's two square-root tails give a finite deterministic signed rate
along every natural planar direction, with almost-sure, L1 and expected-rate
convergence for the actual terminal-excluded last-passage values. -/
theorem exists_lastPassage_ray_convergence_of_martin_tails
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : (∫⁻ t in Iio (0 : ℝ), (μ (Iic t)) ^ (1 / 2 : ℝ)) < ∞)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞)
    (a : ℕ × ℕ) :
    ∃ g : ℝ,
      Tendsto (fun n : ℕ =>
        (∫ ω, lastPassage ω 0 (n • a) ∂environmentLaw μ) / (n : ℝ))
        atTop (𝓝 g) ∧
      g = sSup (range (fun n : ℕ =>
        (∫ ω, lastPassage ω 0 ((n + 1) • a) ∂environmentLaw μ) /
          ((n + 1 : ℕ) : ℝ))) ∧
      (∀ᵐ ω ∂environmentLaw μ, Tendsto
        (fun n : ℕ => lastPassage ω 0 (n • a) / (n : ℝ)) atTop (𝓝 g)) ∧
      Tendsto (fun n : ℕ => ∫ ω,
        |lastPassage ω 0 (n • a) / (n : ℝ) - g| ∂environmentLaw μ)
        atTop (𝓝 0) := by
  have hμ := integrable_id_of_martin_tails μ hneg hpos
  obtain ⟨C, hC, hbound⟩ := exists_positive_animalMaximum_mean_bound
  let I : ℝ≥0∞ := ∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)
  refine exists_lastPassage_ray_convergence_of_expected_bound μ hμ a
    (C * ((a.1 + a.2 : ℕ) : ℝ) * I.toReal) ?_
  intro n _hn
  by_cases hd : 0 < (n • a).1 + (n • a).2
  · have hN : 1 ≤ (n • a).1 + (n • a).2 := by omega
    have hmoment := (hbound μ ((n • a).1 + (n • a).2) hN).2 hpos
    calc
      (∫ ω, lastPassage ω 0 (n • a) ∂environmentLaw μ) ≤
          ∫ ω, animalMaximum ((n • a).1 + (n • a).2) hN
            (fun v => max (ω v) 0) ∂environmentLaw μ := by
        apply integral_mono (integrable_lastPassage μ hμ 0 (n • a)) hmoment.1
        intro ω
        exact lastPassage_le_animalMaximum_atOrigin ω (n • a) hd
      _ ≤ C * (((n • a).1 + (n • a).2 : ℕ) : ℝ) * I.toReal := hmoment.2
      _ = (C * ((a.1 + a.2 : ℕ) : ℝ) * I.toReal) * (n : ℝ) := by
        simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
          Nat.cast_add, Nat.cast_mul]
        ring
  · have hd0 : n • a = 0 := by
      apply Prod.ext
      · change (n • a).1 = 0
        omega
      · change (n • a).2 = 0
        omega
    rw [hd0]
    change (∫ ω, lastPassage ω 0 (0, 0) ∂environmentLaw μ) ≤ _
    simp only [lastPassage_zero, integral_zero]
    positivity

end LPPDifferentiability
