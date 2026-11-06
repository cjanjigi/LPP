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

theorem source_top_indicator_event_measurable (μ : Measure ℝ) :
    MeasurableSet {t : ℝ | (t : EReal) =
      sSup ((fun s : ℝ => (s : EReal)) '' μ.support)} :=
  measurableSet_eq_fun measurable_coe_real_ereal measurable_const

theorem source_top_indicator_eq_indicator (μ : Measure ℝ) :
    (fun t : ℝ => if (t : EReal) =
        sSup ((fun s : ℝ => (s : EReal)) '' μ.support) then (1 : ℝ) else 0) =
      {t : ℝ | (t : EReal) =
        sSup ((fun s : ℝ => (s : EReal)) '' μ.support)}.indicator (fun _ => (1 : ℝ)) := by
  classical
  funext t
  simp only [Set.indicator_apply, mem_ofPred_eq]

theorem measurable_source_top_indicator (μ : Measure ℝ) :
    Measurable (fun t : ℝ => if (t : EReal) =
      sSup ((fun s : ℝ => (s : EReal)) '' μ.support) then (1 : ℝ) else 0) := by
  exact Measurable.ite (source_top_indicator_event_measurable μ)
    measurable_const measurable_const

theorem source_top_indicator_zero_or_one (μ : Measure ℝ) (t : ℝ) :
    (if (t : EReal) = sSup ((fun s : ℝ => (s : EReal)) '' μ.support)
      then (1 : ℝ) else 0) = 0 ∨
    (if (t : EReal) = sSup ((fun s : ℝ => (s : EReal)) '' μ.support)
      then (1 : ℝ) else 0) = 1 := by
  by_cases h : (t : EReal) = sSup ((fun s : ℝ => (s : EReal)) '' μ.support)
  · simp [h]
  · simp [h]

theorem source_top_indicator_mem_unitInterval (μ : Measure ℝ) (t : ℝ) :
    (if (t : EReal) = sSup ((fun s : ℝ => (s : EReal)) '' μ.support)
      then (1 : ℝ) else 0) ∈ Icc (0 : ℝ) 1 := by
  rcases source_top_indicator_zero_or_one μ t with h | h <;> rw [h] <;> norm_num

theorem source_top_mass_mem_unitInterval (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    μ.real {t : ℝ | (t : EReal) =
      sSup ((fun s : ℝ => (s : EReal)) '' μ.support)} ∈ Icc (0 : ℝ) 1 :=
  ⟨measureReal_nonneg, measureReal_le_one⟩

theorem source_top_indicator_hasLaw (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    HasLaw
      (fun t : ℝ => if (t : EReal) =
        sSup ((fun s : ℝ => (s : EReal)) '' μ.support) then (1 : ℝ) else 0)
      (bernoulliMeasure (1 : ℝ) 0
        ⟨μ.real {t : ℝ | (t : EReal) =
          sSup ((fun s : ℝ => (s : EReal)) '' μ.support)}, by simp⟩)
      μ := by
  rw [source_top_indicator_eq_indicator μ]
  exact hasLaw_indicator_one_bernoulliMeasure
    (source_top_indicator_event_measurable μ).nullMeasurableSet

theorem measurable_source_top_indicator_environment (μ : Measure ℝ) :
    Measurable (fun ω : Environment => fun z : Lattice =>
      if (ω z : EReal) = sSup ((fun s : ℝ => (s : EReal)) '' μ.support)
        then (1 : ℝ) else 0) :=
  measurable_coordinatewise_environment_map
    (fun t : ℝ => if (t : EReal) =
      sSup ((fun s : ℝ => (s : EReal)) '' μ.support) then (1 : ℝ) else 0)
    (measurable_source_top_indicator μ)

theorem source_top_indicator_environment_eval_independent (μ : Measure ℝ)
    [IsProbabilityMeasure μ] :
    iIndepFun
      (fun z (ω : Environment) => if (ω z : EReal) =
        sSup ((fun s : ℝ => (s : EReal)) '' μ.support) then (1 : ℝ) else 0)
      (environmentLaw μ) := by
  exact iIndepFun_coordinatewise_environment_eval μ
    (fun t : ℝ => if (t : EReal) =
      sSup ((fun s : ℝ => (s : EReal)) '' μ.support) then (1 : ℝ) else 0)
    (measurable_source_top_indicator μ)

theorem environmentLaw_map_source_top_indicator_eval (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (z : Lattice) :
    (environmentLaw μ).map
      (fun ω : Environment => if (ω z : EReal) =
        sSup ((fun s : ℝ => (s : EReal)) '' μ.support) then (1 : ℝ) else 0) =
      μ.map (fun t : ℝ => if (t : EReal) =
        sSup ((fun s : ℝ => (s : EReal)) '' μ.support) then (1 : ℝ) else 0) := by
  exact environmentLaw_map_coordinatewise_eval μ
    (fun t : ℝ => if (t : EReal) =
      sSup ((fun s : ℝ => (s : EReal)) '' μ.support) then (1 : ℝ) else 0)
    (measurable_source_top_indicator μ) z

theorem source_top_indicator_environment_eval_hasLaw (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (z : Lattice) :
    HasLaw
      (fun ω : Environment => if (ω z : EReal) =
        sSup ((fun s : ℝ => (s : EReal)) '' μ.support) then (1 : ℝ) else 0)
      (bernoulliMeasure (1 : ℝ) 0
        ⟨μ.real {t : ℝ | (t : EReal) =
          sSup ((fun s : ℝ => (s : EReal)) '' μ.support)}, by simp⟩)
      (environmentLaw μ) := by
  refine ⟨(measurable_source_top_indicator μ).comp (measurable_environment_eval z) |>.aemeasurable,
    ?_⟩
  calc
    (environmentLaw μ).map
        (fun ω : Environment => if (ω z : EReal) =
          sSup ((fun s : ℝ => (s : EReal)) '' μ.support) then (1 : ℝ) else 0) =
        μ.map (fun t : ℝ => if (t : EReal) =
          sSup ((fun s : ℝ => (s : EReal)) '' μ.support) then (1 : ℝ) else 0) :=
      environmentLaw_map_source_top_indicator_eval μ z
    _ = bernoulliMeasure (1 : ℝ) 0
        ⟨μ.real {t : ℝ | (t : EReal) =
          sSup ((fun s : ℝ => (s : EReal)) '' μ.support)}, by simp⟩ :=
      (source_top_indicator_hasLaw μ).map_eq

theorem source_top_indicator_environmentLaw_map (μ : Measure ℝ)
    [IsProbabilityMeasure μ] :
    (environmentLaw μ).map
      (fun ω : Environment => fun z : Lattice => if (ω z : EReal) =
        sSup ((fun s : ℝ => (s : EReal)) '' μ.support) then (1 : ℝ) else 0) =
      environmentLaw (μ.map (fun t : ℝ => if (t : EReal) =
        sSup ((fun s : ℝ => (s : EReal)) '' μ.support) then (1 : ℝ) else 0)) := by
  exact environmentLaw_map_coordinatewise μ
    (fun t : ℝ => if (t : EReal) =
      sSup ((fun s : ℝ => (s : EReal)) '' μ.support) then (1 : ℝ) else 0)
    (measurable_source_top_indicator μ)

theorem source_top_indicator_map_ae_mem_unitInterval (μ : Measure ℝ)
    [IsProbabilityMeasure μ] :
    ∀ᵐ y : ℝ ∂μ.map (fun t : ℝ => if (t : EReal) =
      sSup ((fun s : ℝ => (s : EReal)) '' μ.support) then (1 : ℝ) else 0),
      y ∈ Icc (0 : ℝ) 1 := by
  exact (ae_map_iff
      (f := fun t : ℝ => if (t : EReal) =
        sSup ((fun s : ℝ => (s : EReal)) '' μ.support) then (1 : ℝ) else 0)
      (μ := μ) (p := fun y : ℝ => y ∈ Icc (0 : ℝ) 1)
      (measurable_source_top_indicator μ).aemeasurable measurableSet_Icc).2
    (Filter.Eventually.of_forall (source_top_indicator_mem_unitInterval μ))

theorem source_top_indicator_eq_zero_of_endpoint_top (μ : Measure ℝ)
    (hM : sSup ((fun s : ℝ => (s : EReal)) '' μ.support) = ⊤) :
    ∀ t : ℝ, (if (t : EReal) =
      sSup ((fun s : ℝ => (s : EReal)) '' μ.support) then (1 : ℝ) else 0) = 0 := by
  intro t
  simp only [hM, EReal.coe_ne_top, ite_false]

theorem source_top_mass_eq_zero_of_endpoint_top (μ : Measure ℝ)
    (hM : sSup ((fun s : ℝ => (s : EReal)) '' μ.support) = ⊤) :
    μ.real {t : ℝ | (t : EReal) =
      sSup ((fun s : ℝ => (s : EReal)) '' μ.support)} = 0 := by
  rw [source_top_atom_eq_empty_of_support_sSup_eq_top μ hM]
  simp

theorem source_top_indicator_hasLaw_dirac_zero_of_endpoint_top (μ : Measure ℝ)
    [IsProbabilityMeasure μ]
    (hM : sSup ((fun s : ℝ => (s : EReal)) '' μ.support) = ⊤) :
    HasLaw
      (fun t : ℝ => if (t : EReal) =
        sSup ((fun s : ℝ => (s : EReal)) '' μ.support) then (1 : ℝ) else 0)
      (Measure.dirac 0) μ := by
  refine ⟨(measurable_source_top_indicator μ).aemeasurable, ?_⟩
  have hzero : (fun t : ℝ => if (t : EReal) =
      sSup ((fun s : ℝ => (s : EReal)) '' μ.support) then (1 : ℝ) else 0) =
      fun _ => (0 : ℝ) := by
    funext t
    exact source_top_indicator_eq_zero_of_endpoint_top μ hM t
  rw [hzero]
  simp

theorem source_top_indicator_environment_field_eq_zero_of_endpoint_top (μ : Measure ℝ)
    (hM : sSup ((fun s : ℝ => (s : EReal)) '' μ.support) = ⊤) :
    ∀ ω : Environment,
      (fun z : Lattice => if (ω z : EReal) =
        sSup ((fun s : ℝ => (s : EReal)) '' μ.support) then (1 : ℝ) else 0) =
      fun _ => (0 : ℝ) := by
  intro ω
  funext z
  exact source_top_indicator_eq_zero_of_endpoint_top μ hM (ω z)

end LPPDifferentiability

end
