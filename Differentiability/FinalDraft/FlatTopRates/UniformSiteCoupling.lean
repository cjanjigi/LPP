/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.Model.OrientedPercolation
public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.Probability.Distributions.Bernoulli
import all Differentiability.FinalDraft.FlatTop.SurvivalLaw
import LPP_Foundations.Probability.EnvironmentMap

/-! One independent uniform coordinate at each real-valued site couples the Bernoulli site fields. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace LPPDifferentiability.FinalDraft

/-- The uniform distribution on the closed unit interval, viewed as a probability law on reals. -/
noncomputable def siteUniformMarginal : Measure ℝ :=
  (volume : Measure unitInterval).map (fun u : unitInterval => (u : ℝ))

instance : IsProbabilityMeasure siteUniformMarginal :=
  (Measure.isProbabilityMeasure_map_iff measurable_subtype_coe.aemeasurable).2 inferInstance

/-- Raising a density from `p` to `q` opens the sites whose independent uniform value lies
in `(p,q]`, an event of probability `q - p`. -/
theorem siteUniformMarginal_real_Ioc (p q : unitInterval) (hpq : p ≤ q) :
    siteUniformMarginal.real (Ioc (p : ℝ) (q : ℝ)) = (q : ℝ) - (p : ℝ) := by
  rw [Measure.real_def, siteUniformMarginal,
    Measure.map_apply measurable_subtype_coe measurableSet_Ioc]
  change (volume (Ioc p q)).toReal = (q : ℝ) - (p : ℝ)
  rw [unitInterval.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr hpq)]

/-- The iid real environment law whose coordinates are uniform on the closed unit interval. -/
noncomputable def siteUniformLaw : Measure Environment :=
  environmentLaw siteUniformMarginal

instance : IsProbabilityMeasure siteUniformLaw := by
  unfold siteUniformLaw
  infer_instance

/-- Open sites have uniform value at most the density. The field uses real weights one and zero. -/
noncomputable def thresholdSiteEnvironment (p : unitInterval) (u : Environment) : Environment :=
  fun z => if u z ≤ (p : ℝ) then 1 else 0

/-- The threshold field is measurable in the common uniform environment. -/
theorem measurable_thresholdSiteEnvironment (p : unitInterval) :
    Measurable (thresholdSiteEnvironment p) := by
  have hm : Measurable (fun x : ℝ => if x ≤ (p : ℝ) then (1 : ℝ) else 0) :=
    Measurable.ite measurableSet_Iic measurable_const measurable_const
  exact measurable_coordinatewise_environment_map _ hm

/-- The image of the common uniform law under a density threshold is the iid Bernoulli site law. -/
theorem map_siteUniformLaw_thresholdSiteEnvironment (p : unitInterval) :
    siteUniformLaw.map (thresholdSiteEnvironment p) =
      environmentLaw (bernoulliMeasure (1 : ℝ) 0 p) := by
  let f (x : ℝ) : ℝ := if x ≤ (p : ℝ) then 1 else 0
  have hf : Measurable f := Measurable.ite measurableSet_Iic measurable_const measurable_const
  have hmap : siteUniformMarginal.map f = bernoulliMeasure (1 : ℝ) 0 p := by
    rw [siteUniformMarginal, Measure.map_map hf measurable_subtype_coe]
    exact (uniformThreshold_hasLaw p).map_eq
  unfold siteUniformLaw
  rw [show (environmentLaw siteUniformMarginal).map (thresholdSiteEnvironment p) =
      environmentLaw (siteUniformMarginal.map f) from
    environmentLaw_map_coordinatewise siteUniformMarginal f hf]
  simp only [environmentLaw, hmap]

/-- The actual open sites of the threshold field are the sites below the threshold. -/
theorem mem_topSites_thresholdSiteEnvironment_iff (p : unitInterval)
    (u : Environment) (z : Lattice) :
    z ∈ topSites (thresholdSiteEnvironment p u) ↔ u z ≤ (p : ℝ) := by
  change (if u z ≤ (p : ℝ) then (1 : ℝ) else 0) = 1 ↔ u z ≤ (p : ℝ)
  by_cases hz : u z ≤ (p : ℝ) <;> simp [hz]

/-- Increasing the density can only open more sites in the common uniform environment. -/
theorem topSites_thresholdSiteEnvironment_mono (u : Environment) :
    Monotone (fun p => topSites (thresholdSiteEnvironment p u)) := by
  intro p q hpq z hz
  rw [mem_topSites_thresholdSiteEnvironment_iff] at hz ⊢
  exact hz.trans hpq

end LPPDifferentiability.FinalDraft
