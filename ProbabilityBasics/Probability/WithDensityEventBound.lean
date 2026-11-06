/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import ProbabilityBasics.Probability.CenteredRpowSum

/-!
# Event bounds for a density

The Cauchy–Schwarz step in the change-of-measure estimate of the proof of Lemma 4.2
of the differentiability preprint, applied to the measure obtained from a
nonnegative density. The square moment is an integrability premise; the finite
mass of the weighted measure and the event bound are proved from it.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace LPPDifferentiability

/-- A nonnegative square-integrable density bounds every event under its weighted
measure by the Cauchy–Schwarz product. -/
theorem withDensity_event_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ρ : Ω → ℝ) (hρ : Measurable ρ)
    (hρ_nonneg : ∀ ω, 0 ≤ ρ ω) (hρ_sq : Integrable (fun ω => ρ ω ^ 2) P)
    {A : Set Ω} (hA : MeasurableSet A) :
    (P.withDensity (fun ω => ENNReal.ofReal (ρ ω))).real A ≤
      Real.sqrt (∫ ω, ρ ω ^ 2 ∂P) * Real.sqrt (P.real A) := by
  let Q : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal (ρ ω))
  have hρ_abs_sq : Integrable (fun ω => |ρ ω| ^ (2 : ℝ)) P := by
    simpa only [Real.rpow_two, sq_abs] using hρ_sq
  have hρ_integrable : Integrable ρ P :=
    integrable_of_integrable_abs_rpow P hρ (r := 2) (by norm_num) hρ_abs_sq
  have hQ_finite : IsFiniteMeasure Q := by
    dsimp [Q]
    exact isFiniteMeasure_withDensity_ofReal hρ_integrable.hasFiniteIntegral
  have hρ_mem : MemLp ρ (ENNReal.ofReal (2 : ℝ)) P := by
    apply (integrable_norm_rpow_iff hρ.aestronglyMeasurable (by norm_num) (by norm_num)).mp
    simpa only [ENNReal.toReal_ofReal (by norm_num : 0 ≤ (2 : ℝ)),
      Real.norm_eq_abs, Real.rpow_two, sq_abs] using hρ_sq
  have hρ_mem_A : MemLp ρ (ENNReal.ofReal (2 : ℝ)) (P.restrict A) :=
    hρ_mem.mono_measure Measure.restrict_le_self
  have h1_mem_A : MemLp (fun _ : Ω => (1 : ℝ)) (ENNReal.ofReal (2 : ℝ))
      (P.restrict A) := memLp_const 1
  have hρ_nonneg_A : 0 ≤ᵐ[P.restrict A] ρ :=
    Filter.Eventually.of_forall hρ_nonneg
  have h1_nonneg_A : 0 ≤ᵐ[P.restrict A] (fun _ : Ω => (1 : ℝ)) :=
    Filter.Eventually.of_forall (fun _ => le_of_lt zero_lt_one)
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg
    Real.HolderConjugate.two_two hρ_nonneg_A h1_nonneg_A hρ_mem_A h1_mem_A
  have hcs_event :
      (∫ ω, ρ ω ∂P.restrict A) ≤
        Real.sqrt (∫ ω, ρ ω ^ 2 ∂P.restrict A) * Real.sqrt (P.real A) := by
    simpa only [mul_one, Real.rpow_two, one_pow, Real.one_rpow, integral_const, smul_eq_mul,
      measureReal_restrict_apply_univ, mul_one, ← Real.sqrt_eq_rpow] using hcs
  have hsq_restrict_le :
      (∫ ω, ρ ω ^ 2 ∂P.restrict A) ≤ ∫ ω, ρ ω ^ 2 ∂P :=
    integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall (fun ω => sq_nonneg (ρ ω))) hρ_sq
  have hQ_event : Q A = ENNReal.ofReal (∫ ω, ρ ω ∂P.restrict A) := by
    dsimp [Q]
    rw [withDensity_apply _ hA]
    exact (ofReal_integral_eq_lintegral_ofReal hρ_integrable.restrict
      (Filter.Eventually.of_forall hρ_nonneg)).symm
  have hQ_A_lt_top : Q A < ∞ :=
    (measure_mono (Set.subset_univ A)).trans_lt hQ_finite.measure_univ_lt_top
  have hQ_real_event : Q.real A = ∫ ω, ρ ω ∂P.restrict A := by
    calc
      Q.real A = (ENNReal.ofReal (Q.real A)).toReal :=
        (ENNReal.toReal_ofReal measureReal_nonneg).symm
      _ = (Q A).toReal := congrArg ENNReal.toReal (ofReal_measureReal hQ_A_lt_top.ne)
      _ = (ENNReal.ofReal (∫ ω, ρ ω ∂P.restrict A)).toReal :=
        congrArg ENNReal.toReal hQ_event
      _ = ∫ ω, ρ ω ∂P.restrict A :=
        ENNReal.toReal_ofReal (integral_nonneg (fun ω => hρ_nonneg ω))
  calc
    Q.real A = ∫ ω, ρ ω ∂P.restrict A := hQ_real_event
    _ ≤ Real.sqrt (∫ ω, ρ ω ^ 2 ∂P.restrict A) * Real.sqrt (P.real A) := hcs_event
    _ ≤ Real.sqrt (∫ ω, ρ ω ^ 2 ∂P) * Real.sqrt (P.real A) := by
      apply mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hsq_restrict_le)
      exact Real.sqrt_nonneg _

/-- If the density square moment is at most `exp B`, its event bound has factor
`exp (B / 2)`. -/
theorem withDensity_event_bound_of_integral_sq_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ρ : Ω → ℝ) (hρ : Measurable ρ)
    (hρ_nonneg : ∀ ω, 0 ≤ ρ ω) (hρ_sq : Integrable (fun ω => ρ ω ^ 2) P)
    (B : ℝ) (hcost : (∫ ω, ρ ω ^ 2 ∂P) ≤ Real.exp B)
    {A : Set Ω} (hA : MeasurableSet A) :
    (P.withDensity (fun ω => ENNReal.ofReal (ρ ω))).real A ≤
      Real.exp (B / 2) * Real.sqrt (P.real A) := by
  calc
    (P.withDensity (fun ω => ENNReal.ofReal (ρ ω))).real A ≤
        Real.sqrt (∫ ω, ρ ω ^ 2 ∂P) * Real.sqrt (P.real A) :=
      withDensity_event_bound P ρ hρ hρ_nonneg hρ_sq hA
    _ ≤ Real.sqrt (Real.exp B) * Real.sqrt (P.real A) := by
      exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hcost) (Real.sqrt_nonneg _)
    _ = Real.exp (B / 2) * Real.sqrt (P.real A) := by
      rw [← Real.exp_half]

end LPPDifferentiability
