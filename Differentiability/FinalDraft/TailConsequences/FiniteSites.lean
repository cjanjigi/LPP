/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LPP_Foundations.Probability.CoordinateLaw
public import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

/-! Finite-site tail probabilities used in the fixed-length and endpoint arguments
of the final differentiability draft, Section 4 Remark "The role of n" and subsection `sub:ub_mom-chat`. -/

public section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal BigOperators

namespace LPPDifferentiability.FinalDraft

private theorem measureReal_site_above (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (z : Lattice) (t : ℝ) :
    (environmentLaw μ).real {ω : Environment | t < ω z} = μ.real (Ioi t) := by
  change ((environmentLaw μ) ((fun ω : Environment => ω z) ⁻¹' Ioi t)).toReal = _
  rw [← Measure.map_apply (measurable_environment_eval z) measurableSet_Ioi,
    environmentLaw_map_eval]
  rfl

/-- The union bound for vertices in a fixed finite set, with the actual marginal upper tail. -/
theorem measureReal_exists_site_above_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (S : Finset Lattice) (t : ℝ) :
    (environmentLaw μ).real {ω : Environment | ∃ z ∈ S, t < ω z} ≤
      (S.card : ℝ) * μ.real (Ioi t) := by
  classical
  have hset : {ω : Environment | ∃ z ∈ S, t < ω z} =
      ⋃ z ∈ S, {ω : Environment | t < ω z} := by ext ω; simp
  rw [hset]
  calc
    _ ≤ ∑ z ∈ S, (environmentLaw μ).real {ω : Environment | t < ω z} :=
      measureReal_biUnion_finset_le _ _
    _ = _ := by simp only [measureReal_site_above, Finset.sum_const, nsmul_eq_mul]

/-- Independence gives the exact probability of at least one strict upper exceedance.
The complement uses the closed threshold and therefore includes atoms at the cutoff. -/
theorem measureReal_exists_site_above_eq (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (S : Finset Lattice) (t : ℝ) :
    (environmentLaw μ).real {ω : Environment | ∃ z ∈ S, t < ω z} =
      1 - (1 - μ.real (Ioi t)) ^ S.card := by
  classical
  let good (z : Lattice) : Set Environment := (fun ω => ω z) ⁻¹' Iic t
  have hmeasure (z : Lattice) : (environmentLaw μ) (good z) = μ (Iic t) := by
    change (environmentLaw μ) ((fun ω : Environment => ω z) ⁻¹' Iic t) = _
    rw [← Measure.map_apply (measurable_environment_eval z) measurableSet_Iic,
      environmentLaw_map_eval]
  have hind : (environmentLaw μ) (⋂ z ∈ S, good z) =
      ∏ z ∈ S, (environmentLaw μ) (good z) :=
    (iIndepFun_environment_eval μ).meas_biInter fun z _ =>
      MeasurableSpace.measurableSet_comap.mpr ⟨Iic t, measurableSet_Iic, rfl⟩
  have hP : (environmentLaw μ).real (⋂ z ∈ S, good z) = μ.real (Iic t) ^ S.card := by
    rw [measureReal_def, hind, ENNReal.toReal_prod]
    simp only [hmeasure, ← measureReal_def, Finset.prod_const]
  have hm : MeasurableSet (⋂ z ∈ S, good z) :=
    MeasurableSet.biInter S.countable_toSet fun z _ =>
      measurable_environment_eval z measurableSet_Iic
  have heq : {ω : Environment | ∃ z ∈ S, t < ω z} = (⋂ z ∈ S, good z)ᶜ := by
    ext ω
    simp [good, not_le]
  have htail : μ.real (Iic t) = 1 - μ.real (Ioi t) := by
    simpa only [compl_Ioi] using probReal_compl_eq_one_sub (μ := μ) (measurableSet_Ioi (a := t))
  rw [heq, probReal_compl_eq_one_sub hm, hP, htail]

end LPPDifferentiability.FinalDraft
