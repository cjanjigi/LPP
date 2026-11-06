/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.DiagonalAnimalCenteredLower
public import Martin2004.Probability.DiagonalAnimalArrayLaw
import Martin2004.Probability.DiagonalAnimalArrayInputs
import Martin2004.Probability.BilateralCenteredUpper
import Mathlib.Topology.Order.LiminfLimsup

/-! The original-space centered limit of the actual proper-interval diagonal
animal maxima. The rate and universal bound are the forward witnesses. -/

public section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace LPPDifferentiability

/-- Finite matching extended lower and upper limits give both extended and
ordinary real convergence, without an extra boundedness premise. -/
theorem tendsto_ereal_and_real_of_liminf_limsup_bounds
    {u : ℕ → ℝ} {q : ℝ}
    (hlower : (q : EReal) ≤ liminf (fun n => (u n : EReal)) atTop)
    (hupper : limsup (fun n => (u n : EReal)) atTop ≤ (q : EReal)) :
    Tendsto (fun n => (u n : EReal)) atTop (𝓝 (q : EReal)) ∧
      Tendsto u atTop (𝓝 q) := by
  have h := tendsto_of_le_liminf_of_limsup_le hlower hupper
  exact ⟨h, EReal.tendsto_coe.mp h⟩

/-- The actual forward supremum is the least upper bound of the same
expectations after pushing forward the complete proper-interval array. -/
theorem isLUB_diagonalAnimalArray_origin_rates
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hnonneg : ∀ᵐ x ∂μ, 0 ≤ x)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞)
    {q : ℝ}
    (hsup : q = sSup (range (fun n : ℕ =>
      (∫ ω : Environment, diagonalAnimalMaximum 0 ((n + 1 : ℕ) : ℤ) (by omega) ω
        ∂environmentLaw μ) / ((n + 1 : ℕ) : ℝ)))) :
    IsLUB (range (fun n : ℕ =>
      (∫ x : BilateralArray, x ⟨(0, ((n + 1 : ℕ) : ℤ)), by omega⟩
        ∂((environmentLaw μ).map diagonalAnimalArray)) / (n + 1 : ℝ))) q := by
  have heq (n : ℕ) :
      (∫ x : BilateralArray, x ⟨(0, ((n + 1 : ℕ) : ℤ)), by omega⟩
        ∂((environmentLaw μ).map diagonalAnimalArray)) =
      ∫ ω : Environment, diagonalAnimalMaximum 0 ((n + 1 : ℕ) : ℤ) (by omega) ω
        ∂environmentLaw μ := by
    rw [integral_map measurable_diagonalAnimalArray.aemeasurable
      (measurable_pi_apply ⟨(0, ((n + 1 : ℕ) : ℤ)), by omega⟩).aestronglyMeasurable]
    rfl
  simp_rw [heq]
  rw [hsup]
  simpa only [Nat.cast_add, Nat.cast_one] using
    (isLUB_csSup (range_nonempty _)
      (bddAbove_diagonalAnimalExpectedRates μ hnonneg hpos))

/-- One universal bound and the same actual forward rate give original-space
centered almost-sure convergence at radius n+1, with every forward
and centered lower, mean and L1 conclusion retained. The source premises alone
produce the full array law and all inputs of the joint-majorant upper bound. -/
theorem exists_diagonalAnimalMaximum_forward_and_centered_convergence :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
      (∀ᵐ x ∂μ, 0 ≤ x) →
      (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞ →
      ∃ q : ℝ, 0 ≤ q ∧
        q ≤ C * (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)).toReal ∧
        Tendsto (fun n : ℕ =>
          (∫ ω, diagonalAnimalMaximum 0 ((n + 1 : ℕ) : ℤ) (by omega) ω
            ∂environmentLaw μ) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 q) ∧
        q = sSup (range (fun n : ℕ =>
          (∫ ω, diagonalAnimalMaximum 0 ((n + 1 : ℕ) : ℤ) (by omega) ω
            ∂environmentLaw μ) / ((n + 1 : ℕ) : ℝ))) ∧
        (∀ᵐ ω ∂environmentLaw μ, Tendsto (fun n : ℕ =>
          diagonalAnimalMaximum 0 ((n + 1 : ℕ) : ℤ) (by omega) ω /
            ((n + 1 : ℕ) : ℝ)) atTop (𝓝 q)) ∧
        Tendsto (fun n : ℕ => ∫ ω,
          |diagonalAnimalMaximum 0 ((n + 1 : ℕ) : ℤ) (by omega) ω /
            ((n + 1 : ℕ) : ℝ) - q| ∂environmentLaw μ) atTop (𝓝 0) ∧
        (∀ᵐ ω ∂environmentLaw μ, (q : EReal) ≤
          liminf (fun n => (diagonalAnimalCenteredRate n ω : EReal)) atTop) ∧
        Tendsto (fun n => ∫ ω, diagonalAnimalCenteredRate n ω ∂environmentLaw μ)
          atTop (𝓝 q) ∧
        Tendsto (fun n => ∫ ω, |diagonalAnimalCenteredRate n ω - q| ∂environmentLaw μ)
          atTop (𝓝 0) ∧
        (∀ᵐ ω ∂environmentLaw μ,
          limsup (fun n => (diagonalAnimalCenteredRate n ω : EReal)) atTop ≤ (q : EReal)) ∧
        (∀ᵐ ω ∂environmentLaw μ, Tendsto
          (fun n => (diagonalAnimalCenteredRate n ω : EReal)) atTop (𝓝 (q : EReal))) ∧
        (∀ᵐ ω ∂environmentLaw μ,
          Tendsto (fun n => diagonalAnimalCenteredRate n ω) atTop (𝓝 q)) := by
  obtain ⟨C, hC, hsource⟩ :=
    exists_diagonalAnimalMaximum_forward_and_centered_lower_convergence
  refine ⟨C, hC, ?_⟩
  intro μ _ hnonneg hpos
  obtain ⟨q, hq, hqbound, hmean, hsup, hforward, hL1, hlower, hcenteredMean,
      hcenteredL1⟩ := hsource μ hnonneg hpos
  have hμ := integrable_id_of_nonneg_positive_sqrt_tail μ hnonneg hpos
  let ρ : ProbabilityMeasure BilateralArray :=
    ⟨(environmentLaw μ).map diagonalAnimalArray, inferInstance⟩
  have hS : MeasurePreserving bilateralArrayShift (ρ : Measure _) (ρ : Measure _) :=
    measurePreserving_bilateralArrayShift_diagonalAnimalArray μ
  have hi (v : BilateralInterval) :
      Integrable (fun x : BilateralArray => x v) (ρ : Measure _) :=
    integrable_diagonalAnimalArray_eval μ hμ v.val.1 v.val.2 v.property
  obtain ⟨B, _hB0, hB⟩ := exists_finite_diagonalAnimalArray_origin_rate_bound
    μ hnonneg hpos
  have hupperArray := ae_bilateralArray_centered_limsup_le ρ hS hi
    (ae_diagonalAnimalArray_nonneg μ hnonneg)
    (ae_diagonalAnimalArray_superadditive μ) B
    (fun n => by
      simpa only [ρ, ProbabilityMeasure.coe_mk, Nat.cast_add, Nat.cast_one] using hB n) q
    (isLUB_diagonalAnimalArray_origin_rates μ hnonneg hpos hsup)
    (ae_diagonalAnimalArray_origin_rate_tendsto_of_environment μ hforward)
  have hupper : ∀ᵐ ω ∂environmentLaw μ,
      limsup (fun n => (diagonalAnimalCenteredRate n ω : EReal)) atTop ≤
        (q : EReal) := by
    apply ae_diagonalAnimalCenteredRate_limsup_le_of_array μ
    simpa only [ρ, ProbabilityMeasure.coe_mk, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_add, Nat.cast_one] using hupperArray
  have hconvergence : ∀ᵐ ω ∂environmentLaw μ,
      Tendsto (fun n => (diagonalAnimalCenteredRate n ω : EReal)) atTop (𝓝 (q : EReal)) ∧
        Tendsto (fun n => diagonalAnimalCenteredRate n ω) atTop (𝓝 q) := by
    filter_upwards [hlower, hupper] with ω hlo hup
    exact tendsto_ereal_and_real_of_liminf_limsup_bounds hlo hup
  exact ⟨q, hq, hqbound, hmean, hsup, hforward, hL1, hlower, hcenteredMean,
    hcenteredL1, hupper, hconvergence.mono (fun _ h => h.1),
    hconvergence.mono (fun _ h => h.2)⟩

end LPPDifferentiability
