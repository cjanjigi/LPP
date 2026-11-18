/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Probability.EnvironmentMap
public import ProbabilityBasics.Probability.SupportTopCDF
public import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Tactic.NormNum

/-!
# The top-weight indicator law

The top of the support of a weight law is the supremum of that support, taken
in `EReal`. The indicator that a site's weight equals this top is a Bernoulli
variable. This file proves its law at one site, and the law of the whole
environment of such indicators under the product measure.
-/

public section

open MeasureTheory ProbabilityTheory Set

namespace LPPDifferentiability

/-- The indicator of a real weight equal to the top of the support of `μ`.
This is the site indicator of the differentiability preprint, Section 2.3. -/
@[expose] noncomputable def topWeightIndicator (μ : Measure ℝ) (t : ℝ) : ℝ :=
  if (t : EReal) = supportTop μ then 1 else 0

/-- Apply the top-weight indicator at each site of the original environment.
Its marginal image law is `μ.map (topWeightIndicator μ)`. -/
@[expose] noncomputable def topWeightIndicatorField (μ : Measure ℝ) (ω : Environment) :
    Environment :=
  fun z => topWeightIndicator μ (ω z)

theorem source_top_indicator_event_measurable (μ : Measure ℝ) :
    MeasurableSet (supportTopAtom μ) :=
  measurableSet_eq_fun measurable_coe_real_ereal measurable_const

theorem source_top_indicator_eq_indicator (μ : Measure ℝ) :
    topWeightIndicator μ = (supportTopAtom μ).indicator (fun _ => (1 : ℝ)) := by
  classical
  funext t
  simp only [topWeightIndicator, Set.indicator_apply, supportTopAtom, mem_ofPred_eq]

theorem measurable_source_top_indicator (μ : Measure ℝ) :
    Measurable (topWeightIndicator μ) :=
  Measurable.ite (source_top_indicator_event_measurable μ) measurable_const measurable_const

theorem source_top_indicator_zero_or_one (μ : Measure ℝ) (t : ℝ) :
    topWeightIndicator μ t = 0 ∨ topWeightIndicator μ t = 1 := by
  by_cases h : (t : EReal) = supportTop μ <;> simp [topWeightIndicator, h]

theorem source_top_indicator_mem_unitInterval (μ : Measure ℝ) (t : ℝ) :
    topWeightIndicator μ t ∈ Icc (0 : ℝ) 1 := by
  rcases source_top_indicator_zero_or_one μ t with h | h <;> rw [h] <;> norm_num

theorem source_top_mass_mem_unitInterval (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    μ.real (supportTopAtom μ) ∈ Icc (0 : ℝ) 1 :=
  ⟨measureReal_nonneg, measureReal_le_one⟩

theorem source_top_indicator_hasLaw (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    HasLaw (topWeightIndicator μ)
      (bernoulliMeasure (1 : ℝ) 0 ⟨μ.real (supportTopAtom μ), by simp⟩) μ := by
  rw [source_top_indicator_eq_indicator μ]
  exact hasLaw_indicator_one_bernoulliMeasure
    (source_top_indicator_event_measurable μ).nullMeasurableSet

theorem measurable_source_top_indicator_environment (μ : Measure ℝ) :
    Measurable (topWeightIndicatorField μ) :=
  measurable_coordinatewise_environment_map (topWeightIndicator μ)
    (measurable_source_top_indicator μ)

theorem source_top_indicator_environment_eval_independent (μ : Measure ℝ)
    [IsProbabilityMeasure μ] :
    iIndepFun (fun z ω => topWeightIndicatorField μ ω z) (environmentLaw μ) :=
  iIndepFun_coordinatewise_environment_eval μ (topWeightIndicator μ)
    (measurable_source_top_indicator μ)

theorem environmentLaw_map_source_top_indicator_eval (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (z : Lattice) :
    (environmentLaw μ).map (fun ω => topWeightIndicatorField μ ω z) =
      μ.map (topWeightIndicator μ) :=
  environmentLaw_map_coordinatewise_eval μ (topWeightIndicator μ)
    (measurable_source_top_indicator μ) z

theorem source_top_indicator_environment_eval_hasLaw (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (z : Lattice) :
    HasLaw (fun ω => topWeightIndicatorField μ ω z)
      (bernoulliMeasure (1 : ℝ) 0 ⟨μ.real (supportTopAtom μ), by simp⟩) (environmentLaw μ) := by
  refine ⟨((measurable_source_top_indicator μ).comp (measurable_environment_eval z)).aemeasurable,
    ?_⟩
  calc
    (environmentLaw μ).map (fun ω => topWeightIndicatorField μ ω z) =
        μ.map (topWeightIndicator μ) := environmentLaw_map_source_top_indicator_eval μ z
    _ = bernoulliMeasure (1 : ℝ) 0 ⟨μ.real (supportTopAtom μ), by simp⟩ :=
      (source_top_indicator_hasLaw μ).map_eq

theorem source_top_indicator_environmentLaw_map (μ : Measure ℝ)
    [IsProbabilityMeasure μ] :
    (environmentLaw μ).map (topWeightIndicatorField μ) =
      environmentLaw (μ.map (topWeightIndicator μ)) :=
  environmentLaw_map_coordinatewise μ (topWeightIndicator μ)
    (measurable_source_top_indicator μ)

theorem source_top_indicator_map_ae_mem_unitInterval (μ : Measure ℝ)
    [IsProbabilityMeasure μ] :
    ∀ᵐ y : ℝ ∂μ.map (topWeightIndicator μ), y ∈ Icc (0 : ℝ) 1 :=
  (ae_map_iff (f := topWeightIndicator μ)
      (μ := μ) (p := fun y : ℝ => y ∈ Icc (0 : ℝ) 1)
      (measurable_source_top_indicator μ).aemeasurable measurableSet_Icc).2
    (Filter.Eventually.of_forall (source_top_indicator_mem_unitInterval μ))

theorem source_top_indicator_eq_zero_of_endpoint_top (μ : Measure ℝ)
    (hM : supportTop μ = ⊤) :
    ∀ t : ℝ, topWeightIndicator μ t = 0 := by
  intro t
  simp only [topWeightIndicator, hM, EReal.coe_ne_top, ite_false]

theorem source_top_mass_eq_zero_of_endpoint_top (μ : Measure ℝ)
    (hM : supportTop μ = ⊤) :
    μ.real (supportTopAtom μ) = 0 := by
  rw [source_top_atom_eq_empty_of_support_sSup_eq_top μ hM]
  simp

theorem source_top_indicator_hasLaw_dirac_zero_of_endpoint_top (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hM : supportTop μ = ⊤) :
    HasLaw (topWeightIndicator μ) (Measure.dirac 0) μ := by
  refine ⟨(measurable_source_top_indicator μ).aemeasurable, ?_⟩
  have hzero : topWeightIndicator μ = fun _ => (0 : ℝ) :=
    funext (source_top_indicator_eq_zero_of_endpoint_top μ hM)
  rw [hzero]
  simp

theorem source_top_indicator_environment_field_eq_zero_of_endpoint_top (μ : Measure ℝ)
    (hM : supportTop μ = ⊤) :
    ∀ ω : Environment, topWeightIndicatorField μ ω = fun _ => (0 : ℝ) := by
  intro ω
  funext z
  exact source_top_indicator_eq_zero_of_endpoint_top μ hM (ω z)

end LPPDifferentiability

end
