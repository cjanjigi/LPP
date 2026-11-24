/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.ExcessFourthMoment
public import Differentiability.FinalDraft.ExcessScaling.IndependentMoment
public import Differentiability.FinalDraft.ExcessScaling.IntegratedTail
import Mathlib.Tactic

/-! Real-order tails for the actual excess sum on a finite block. -/

public section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace LPPDifferentiability

/-- For the source cutoff `η * s / 4` and up to `44 * s ^ (1 + γ)` sites,
the integrated square-root tail is bounded by the two stated powers of the
scale. This is the real-order block calculation in subsection `sub:ub_mom-chat`, using the actual
truncation and site law of Lemma `lem:multiplicity-general` and its one-step bound. -/
theorem exists_excess_sum_integrated_sqrt_tail_bound_of_aspect_ratio
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {p η : ℝ}
    (hp : 2 < p) (hη : 0 < η)
    (hmoment : (∫⁻ x, ENNReal.ofReal ((max x 0) ^ p) ∂μ) < ∞) :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ s : ℝ), 3 ≤ s → ∀ Q : Finset Lattice,
      (Q.card : ℝ) ≤ 44 * s ^ (1 + γ) →
      (∫⁻ t in Ioi (0 : ℝ), (environmentLaw μ)
        {ω : Environment | t < ∑ z ∈ Q, max (ω z - η * s / 4) 0} ^ (1 / 2 : ℝ)) ≤
        ENNReal.ofReal (C * (s ^ ((1 + γ) / p) + s ^ (2 + γ - p))) := by
  obtain ⟨K, hK, hIndependent⟩ := exists_nonnegative_independent_sum_rpow_bound hp
  let Cp : ℝ := ∫ x : ℝ, (max x 0) ^ p ∂μ
  let D₁ : ℝ := 44 * Cp
  let D₂ : ℝ := D₁ * (η / 4) ^ (1 - p)
  let H : ℝ := 1 + K * (D₁ ^ p⁻¹ + D₂)
  let T : ℝ := 1 + (p / 2 - 1)⁻¹
  have hCp : 0 ≤ Cp := integral_nonneg fun x => Real.rpow_nonneg (le_max_right x 0) _
  have hD₁ : 0 ≤ D₁ := by dsimp [D₁]; positivity
  have hD₂ : 0 ≤ D₂ := by dsimp [D₂]; positivity
  have hH : 0 < H := by dsimp [H]; positivity
  have hdenom : 0 < p / 2 - 1 := by linarith only [hp]
  have hT : 0 < T := by dsimp [T]; positivity
  refine ⟨H * T, mul_pos hH hT, ?_⟩
  intro γ s hs Q hcard
  have hp0 : 0 < p := by linarith only [hp]
  have hp1 : 1 ≤ p := by linarith only [hp]
  have hs0 : 0 < s := by linarith only [hs]
  let M : ℝ := η * s / 4
  let φ : ℝ → ℝ := fun x => max (x - M) 0
  let Y : Lattice → Environment → ℝ := fun z ω => φ (ω z)
  let Z : Environment → ℝ := fun ω => ∑ z ∈ Q, Y z ω
  have hM : 0 < M := by dsimp [M]; positivity
  have hφ : Measurable φ := (measurable_id.sub_const M).max measurable_const
  have hY (z : Lattice) : Measurable (Y z) := hφ.comp (measurable_environment_eval z)
  have hY0 (z : Lattice) (ω : Environment) : 0 ≤ Y z ω := le_max_right _ _
  have hZ0 (ω : Environment) : 0 ≤ Z ω := Finset.sum_nonneg fun z _ => hY0 z ω
  have hcoord (z : Lattice) : MeasurePreserving (fun ω : Environment => ω z)
      (environmentLaw μ) μ :=
    ⟨measurable_environment_eval z, environmentLaw_map_eval μ z⟩
  have hpInt : Integrable (fun x => φ x ^ p) μ :=
    integrable_truncated_positive_rpow μ hp0 hp0 le_rfl hM hmoment

  -- Apply the real-order independent sum estimate to the truncated site weights.
  obtain ⟨hZInt, hZRoot⟩ := hIndependent (environmentLaw μ) Q Y hY hY0
    (iIndepFun_coordinatewise_environment_eval μ φ hφ)
    (fun z _ => (hcoord z).integrable_comp_of_integrable hpInt)
  have hmarginal (z : Lattice) {q : ℝ} (hq : 0 ≤ q) :
      (∫ ω : Environment, Y z ω ^ q ∂environmentLaw μ) = ∫ x, φ x ^ q ∂μ := by
    have hmeas : AEStronglyMeasurable (fun x : ℝ => φ x ^ q)
        ((environmentLaw μ).map (fun ω : Environment => ω z)) :=
      ((Real.continuous_rpow_const hq).measurable.comp hφ).aestronglyMeasurable
    calc
      _ = ∫ x, φ x ^ q ∂(environmentLaw μ).map (fun ω : Environment => ω z) :=
        (integral_map (measurable_environment_eval z).aemeasurable hmeas).symm
      _ = _ := by rw [environmentLaw_map_eval]
  have hmean (z : Lattice) :
      (∫ ω : Environment, Y z ω ∂environmentLaw μ) = ∫ x, φ x ∂μ := by
    simpa only [Real.rpow_one] using hmarginal z (q := 1) zero_le_one
  have hpBound : (∫ x, φ x ^ p ∂μ) ≤ Cp := by
    simpa only [sub_self, Real.rpow_zero, mul_one] using
      integral_truncated_positive_rpow_le μ hp0 hp0 le_rfl hM hmoment
  have h1Bound : (∫ x, φ x ∂μ) ≤ Cp * M ^ (1 - p) := by
    simpa only [Real.rpow_one] using
      integral_truncated_positive_rpow_le μ hp0 zero_lt_one hp1 hM hmoment

  -- The summed pth moments contribute the root of the block size; the
  -- summed means also carry the truncation factor `M ^ (1 - p)`.
  have hA : (∑ z ∈ Q, ∫ ω : Environment, Y z ω ^ p ∂environmentLaw μ) ≤
      D₁ * s ^ (1 + γ) := by
    calc
      _ = (Q.card : ℝ) * (∫ x, φ x ^ p ∂μ) := by
        simp only [hmarginal _ hp0.le, Finset.sum_const, nsmul_eq_mul]
      _ ≤ (44 * s ^ (1 + γ)) * Cp :=
        mul_le_mul hcard hpBound (integral_nonneg fun x => Real.rpow_nonneg (le_max_right _ _) _)
          (by positivity)
      _ = _ := by dsimp [D₁]; ring
  have hB : (∑ z ∈ Q, ∫ ω : Environment, Y z ω ∂environmentLaw μ) ≤
      D₂ * s ^ (2 + γ - p) := by
    calc
      _ = (Q.card : ℝ) * (∫ x, φ x ∂μ) := by
        simp only [hmean, Finset.sum_const, nsmul_eq_mul]
      _ ≤ (44 * s ^ (1 + γ)) * (Cp * M ^ (1 - p)) :=
        mul_le_mul hcard h1Bound (integral_nonneg fun x => le_max_right _ _) (by positivity)
      _ = _ := by
        dsimp [M, D₂, D₁]
        rw [show η * s / 4 = (η / 4) * s by ring,
          Real.mul_rpow (by positivity : 0 ≤ η / 4) hs0.le,
          show 2 + γ - p = (1 + γ) + (1 - p) by ring, Real.rpow_add hs0 (1 + γ) (1 - p)]
        ring
  have hA0 : 0 ≤ ∑ z ∈ Q, ∫ ω : Environment, Y z ω ^ p ∂environmentLaw μ :=
    Finset.sum_nonneg fun z _ => integral_nonneg fun ω => Real.rpow_nonneg (hY0 z ω) _
  have hARoot : (∑ z ∈ Q, ∫ ω : Environment, Y z ω ^ p ∂environmentLaw μ) ^ p⁻¹ ≤
      D₁ ^ p⁻¹ * s ^ ((1 + γ) / p) := by
    have hroot := Real.rpow_le_rpow hA0 hA (inv_nonneg.mpr hp0.le)
    rwa [Real.mul_rpow hD₁ (Real.rpow_nonneg hs0.le _), ← Real.rpow_mul hs0.le,
      ← div_eq_mul_inv] at hroot

  -- A positive cutoff for the tail integral can be chosen even if all
  -- truncated weights vanish.
  let a : ℝ := H * (s ^ ((1 + γ) / p) + s ^ (2 + γ - p))
  have ha : 0 < a := by dsimp [a]; positivity
  have hRootBound : (∫ ω, Z ω ^ p ∂environmentLaw μ) ^ p⁻¹ ≤ a := by
    calc
      _ ≤ K * ((∑ z ∈ Q, ∫ ω, Y z ω ^ p ∂environmentLaw μ) ^ p⁻¹ +
          ∑ z ∈ Q, ∫ ω, Y z ω ∂environmentLaw μ) := hZRoot
      _ ≤ K * (D₁ ^ p⁻¹ * s ^ ((1 + γ) / p) + D₂ * s ^ (2 + γ - p)) :=
        mul_le_mul_of_nonneg_left (add_le_add hARoot hB) hK.le
      _ = (K * D₁ ^ p⁻¹) * s ^ ((1 + γ) / p) + (K * D₂) * s ^ (2 + γ - p) := by ring
      _ ≤ a := by
        have hH₁ : K * D₁ ^ p⁻¹ ≤ H := by
          dsimp [H]
          linarith only [mul_nonneg hK.le hD₂]
        have hH₂ : K * D₂ ≤ H := by
          dsimp [H]
          linarith only [mul_nonneg hK.le (Real.rpow_nonneg hD₁ p⁻¹)]
        dsimp [a]
        rw [mul_add]
        exact add_le_add (mul_le_mul_of_nonneg_right hH₁ (by positivity))
          (mul_le_mul_of_nonneg_right hH₂ (by positivity))
  have hMomentBound : (∫ ω, Z ω ^ p ∂environmentLaw μ) ≤ a ^ p :=
    (Real.rpow_inv_le_iff_of_pos (integral_nonneg fun ω => Real.rpow_nonneg (hZ0 ω) _)
      ha.le hp0).mp hRootBound
  have htail := integrated_sqrt_tail_le_of_rpow_moment_bound (environmentLaw μ) Z hZ0
    hp ha hZInt hMomentBound
  change (∫⁻ t in Ioi (0 : ℝ), (environmentLaw μ) {ω : Environment | t < Z ω} ^
      (1 / 2 : ℝ)) ≤ _
  convert htail using 2
  dsimp [a, T]
  ring

end LPPDifferentiability
