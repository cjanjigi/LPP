/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.ERealStochasticMean
public import Mathlib.Topology.Instances.EReal.Lemmas

/-! # Finite representatives and the mean squeeze in Liggett's proof

These elementary helpers supply the finiteness and first-moment justification
between the upper and lower comparisons of Liggett's proof. They do not assume a
finite or integrable origin limit in the theorem.
-/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace LPPDifferentiability

/-- An extended-real variable between two real integrable variables is finite
almost everywhere and has a measurable integrable real representative. -/
theorem exists_integrable_real_of_ereal_sandwich
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {H : Ω → EReal} {l U : Ω → ℝ}
    (hH : Measurable H) (hl : Integrable l μ) (hU : Integrable U μ)
    (hlower : ∀ᵐ ω ∂μ, (l ω : EReal) ≤ H ω)
    (hupper : ∀ᵐ ω ∂μ, H ω ≤ (U ω : EReal)) :
    (∀ᵐ ω ∂μ, H ω ≠ ⊥ ∧ H ω ≠ ⊤) ∧
      ∃ u : Ω → ℝ, Measurable u ∧ Integrable u μ ∧
        (∀ᵐ ω ∂μ, (u ω : EReal) = H ω) ∧
        (∀ᵐ ω ∂μ, l ω ≤ u ω ∧ u ω ≤ U ω) := by
  have hfinite : ∀ᵐ ω ∂μ, H ω ≠ ⊥ ∧ H ω ≠ ⊤ := by
    filter_upwards [hlower, hupper] with ω hlo hup
    constructor
    · intro h
      simp [h] at hlo
    · intro h
      simp [h] at hup
  have hreal : ∀ᵐ ω ∂μ, ((H ω).toReal : EReal) = H ω := by
    filter_upwards [hfinite] with ω hω
    exact EReal.coe_toReal hω.2 hω.1
  have hbetween : ∀ᵐ ω ∂μ, l ω ≤ (H ω).toReal ∧ (H ω).toReal ≤ U ω := by
    filter_upwards [hlower, hupper, hreal] with ω hlo hup hr
    rw [← hr] at hlo hup
    exact ⟨EReal.coe_le_coe_iff.mp hlo, EReal.coe_le_coe_iff.mp hup⟩
  have hint : Integrable (fun ω => (H ω).toReal) μ := by
    apply (hl.abs.add hU.abs).mono' hH.ereal_toReal.aestronglyMeasurable
    filter_upwards [hbetween] with ω hω
    change |(H ω).toReal| ≤ |l ω| + |U ω|
    apply abs_le.mpr
    constructor
    · have := neg_abs_le (l ω)
      have := abs_nonneg (U ω)
      linarith [hω.1]
    · have := le_abs_self (U ω)
      have := abs_nonneg (l ω)
      linarith [hω.2]
  exact ⟨hfinite, (fun ω => (H ω).toReal), hH.ereal_toReal, hint, hreal, hbetween⟩

/-- Ordered integrable variables with squeezed means agree almost everywhere,
and both means are the same prescribed real number. -/
theorem ae_eq_and_integral_eq_of_integral_sandwich
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {l u : Ω → ℝ} {γ : ℝ}
    (hl : Integrable l μ) (hu : Integrable u μ)
    (hle : l ≤ᵐ[μ] u) (hlmean : γ ≤ ∫ ω, l ω ∂μ)
    (humean : (∫ ω, u ω ∂μ) ≤ γ) :
    l =ᵐ[μ] u ∧ (∫ ω, l ω ∂μ) = γ ∧ (∫ ω, u ω ∂μ) = γ := by
  have hmono := integral_mono_ae hl hu hle
  have hlγ : (∫ ω, l ω ∂μ) = γ := le_antisymm (hmono.trans humean) hlmean
  have huγ : (∫ ω, u ω ∂μ) = γ := le_antisymm humean (hlmean.trans hmono)
  exact ⟨(integral_eq_iff_of_ae_le hl hu hle).mp (hlγ.trans huγ.symm), hlγ, huγ⟩

end LPPDifferentiability
