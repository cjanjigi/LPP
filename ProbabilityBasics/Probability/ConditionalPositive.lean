/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Conditional positivity as an event-intersection criterion. -/

@[expose] public section

open MeasureTheory Function

namespace ProbabilityBasics

/-- The conditional expectation of an event indicator is positive almost
everywhere exactly when that event has positive intersection with every
positive event in the conditioning sigma-algebra. This is the probability
criterion used in the finite-block positivity step of GRS arXiv:1510.00860v1,
Appendix A, lines 1466–1470. -/
theorem ae_condExp_indicator_pos_iff
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure[mΩ] Ω) [IsFiniteMeasure P]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (A : Set Ω) (hA : @MeasurableSet Ω mΩ A) :
    (∀ᵐ ω ∂P, 0 < (MeasureTheory.condExp m P
      (A.indicator fun _ : Ω => (1 : ℝ))) ω) ↔
    ∀ H : Set Ω, MeasurableSet[m] H → 0 < P H → 0 < P (A ∩ H) := by
  -- Keep the measure's original measurable space as the ambient instance.
  let : MeasurableSpace Ω := mΩ
  let q : Ω → ℝ := MeasureTheory.condExp m P
    (A.indicator fun _ : Ω => (1 : ℝ))

  -- The indicator is integrable because the ambient measure is finite.
  have h_indicator_integrable :
      Integrable (A.indicator fun _ : Ω => (1 : ℝ)) P :=
    (integrable_const (1 : ℝ)).indicator hA

  -- Conditional expectation preserves nonnegativity and is measurable for `m`.
  have h_indicator_nonneg :
      0 ≤ᵐ[P] A.indicator (fun _ : Ω => (1 : ℝ)) := by
    filter_upwards [] with ω
    by_cases hω : ω ∈ A <;> simp [hω]
  have hq_nonneg : 0 ≤ᵐ[P] q := by
    dsimp [q]
    exact condExp_nonneg h_indicator_nonneg
  have hq_integrable : Integrable q P := by
    dsimp [q]
    exact integrable_condExp
  have hq_strongly_measurable : StronglyMeasurable[m] q := by
    dsimp [q]
    exact stronglyMeasurable_condExp

  -- The conditional-expectation identity converts each event integral to an
  -- intersection measure.
  have h_set_integral (H : Set Ω) (hH : MeasurableSet[m] H) :
      (∫ ω in H, q ω ∂P) = P.real (A ∩ H) := by
    calc
      (∫ ω in H, q ω ∂P) =
          ∫ ω in H, A.indicator (fun _ : Ω => (1 : ℝ)) ω ∂P := by
        dsimp [q]
        exact setIntegral_condExp hm h_indicator_integrable hH
      _ = P.real (A ∩ H) := by
        rw [setIntegral_indicator hA, setIntegral_const]
        simp only [smul_eq_mul, mul_one]
        exact congrArg P.real (Set.inter_comm H A)

  constructor
  · -- Positivity of the conditional expectation gives positive integral on
    -- each positive conditioning event.
    intro hq_pos H hH hH_pos
    have h_support_full : H =ᵐ[P] (support q ∩ H) := by
      filter_upwards [hq_pos] with ω hω
      apply propext
      simp only [Set.mem_inter_iff, Function.mem_support]
      constructor
      · intro hωH
        exact ⟨ne_of_gt hω, hωH⟩
      · intro hω
        exact hω.2
    have h_support_pos : 0 < P (support q ∩ H) := by
      rw [← measure_congr h_support_full]
      exact hH_pos
    have hH_ambient : @MeasurableSet Ω mΩ H := hm H hH
    have hq_nonneg_on_H : 0 ≤ᵐ[P.restrict H] q := by
      rw [Filter.EventuallyLE, ae_restrict_iff' hH_ambient]
      filter_upwards [hq_nonneg] with ω hq_nonneg_at_ω
      intro _hωH
      exact hq_nonneg_at_ω
    have h_integral_pos : 0 < ∫ ω in H, q ω ∂P :=
      (setIntegral_pos_iff_support_of_nonneg_ae hq_nonneg_on_H
        hq_integrable.integrableOn).2 h_support_pos
    have h_intersection_real_pos : 0 < P.real (A ∩ H) := by
      rw [← h_set_integral H hH]
      exact h_integral_pos
    have h_intersection_ne_zero : P (A ∩ H) ≠ 0 := by
      intro h_zero
      have h_real_zero : P.real (A ∩ H) = 0 := by
        simp [Measure.real, h_zero]
      exact (ne_of_gt h_intersection_real_pos) h_real_zero
    exact lt_of_le_of_ne bot_le (Ne.symm h_intersection_ne_zero)
  · -- If a nonpositive set had positive measure, its conditional integral
    -- would be both zero and the positive measure of an intersection.
    intro h_criterion
    let H : Set Ω := {ω | q ω ≤ 0}
    have hH : MeasurableSet[m] H := by
      dsimp [H]
      exact hq_strongly_measurable.measurableSet_le stronglyMeasurable_const
    have hH_ambient : @MeasurableSet Ω mΩ H := hm H hH
    have hq_zero_on_H : q =ᵐ[P.restrict H] 0 := by
      rw [Filter.EventuallyEq, ae_restrict_iff' hH_ambient]
      filter_upwards [hq_nonneg] with ω hq_nonneg_at_ω
      intro hωH
      change q ω ≤ 0 at hωH
      exact le_antisymm hωH hq_nonneg_at_ω
    have h_integral_zero : (∫ ω in H, q ω ∂P) = 0 := by
      rw [integral_congr_ae hq_zero_on_H]
      simp
    have hH_zero : P H = 0 := by
      by_contra hH_ne_zero
      have hH_pos : 0 < P H := lt_of_le_of_ne bot_le (Ne.symm hH_ne_zero)
      have h_intersection_pos := h_criterion H hH hH_pos
      have h_intersection_real_pos : 0 < P.real (A ∩ H) :=
        ENNReal.toReal_pos (ne_of_gt h_intersection_pos) (measure_ne_top P (A ∩ H))
      have h_integral_pos : 0 < ∫ ω in H, q ω ∂P := by
        rw [h_set_integral H hH]
        exact h_intersection_real_pos
      rw [h_integral_zero] at h_integral_pos
      exact (lt_irrefl 0 h_integral_pos)
    rw [ae_iff]
    simpa only [H, not_lt] using hH_zero

end ProbabilityBasics
