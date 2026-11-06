/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.BoundedSumConcentration
public import LPP_Foundations.Probability.PathLaw
public import LPP_Foundations.Frozen.Model.PathWeight
import LPP_Foundations.Probability.PassageIntegrable

/-!
# Concentration along a deterministic path

The collected evaluations are independent because the actual path vertices
are distinct. The endpoint is excluded, so the number of summands is `a+b`.
-/

public section

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

namespace LPPDifferentiability

/-- A bounded marginal bounds each evaluation collected by an actual path. -/
theorem ae_abs_path_collected_eval_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {L : ℝ} (hb : ∀ᵐ x ∂μ, |x| ≤ L) {u : Lattice} {d : ℕ × ℕ}
    (p : Path u d) (i : Fin (d.1 + d.2)) :
    ∀ᵐ ω ∂environmentLaw μ, |ω (p.vertex i.castSucc)| ≤ L := by
  have hm : ∀ᵐ x ∂(environmentLaw μ).map
      (fun ω : Environment => ω (p.vertex i.castSucc)), |x| ≤ L := by
    rw [environmentLaw_map_eval]
    exact hb
  exact ae_of_ae_map (measurable_environment_eval _).aemeasurable hm

/-- Martin's singleton estimate for a deterministic, terminal-excluded path sum. -/
theorem measure_abs_pathWeight_sub_integral_ge_le_martin
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {L t : ℝ} (hL : 0 < L) (ht : 0 < t)
    (hb : ∀ᵐ x ∂μ, |x| ≤ L) {u : Lattice} {d : ℕ × ℕ}
    (p : Path u d) (hd : 0 < d.1 + d.2) :
    (environmentLaw μ).real {ω : Environment |
      t ≤ |pathWeight ω p - ∫ η : Environment, pathWeight η p ∂environmentLaw μ|} ≤
        exp (-t ^ 2 / (64 * (d.1 + d.2 : ℕ) * L ^ 2) + 64) := by
  simpa only [pathWeight, Fintype.card_fin] using
    measure_abs_sum_sub_integral_ge_le_martin
      (fun (i : Fin (d.1 + d.2)) (ω : Environment) => ω (p.vertex i.castSucc))
      hL ht (by simpa only [Fintype.card_fin] using hd)
      (fun _ => measurable_environment_eval _) (iIndepFun_path_collected_eval μ p)
      (ae_abs_path_collected_eval_le μ hb p)

/-- The same estimate centered at the actual finite iid mean, with no moment premise. -/
theorem measure_abs_pathWeight_sub_mean_ge_le_martin
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {L t : ℝ} (hL : 0 < L) (ht : 0 < t)
    (hb : ∀ᵐ x ∂μ, |x| ≤ L) {u : Lattice} {d : ℕ × ℕ}
    (p : Path u d) (hd : 0 < d.1 + d.2) :
    (environmentLaw μ).real {ω : Environment |
      t ≤ |pathWeight ω p - (d.1 + d.2 : ℕ) * ∫ x : ℝ, x ∂μ|} ≤
        exp (-t ^ 2 / (64 * (d.1 + d.2 : ℕ) * L ^ 2) + 64) := by
  have hint : Integrable (fun x : ℝ => x) μ := integrable_of_ae_abs_le measurable_id hb
  simpa only [integral_pathWeight μ hint p] using
    measure_abs_pathWeight_sub_integral_ge_le_martin μ hL ht hb p hd

/-- A path with no collected vertices has no positive centered deviation. -/
theorem measure_abs_pathWeight_sub_integral_ge_eq_zero_of_length_zero
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t)
    {u : Lattice} {d : ℕ × ℕ} (p : Path u d) (hd : d.1 + d.2 = 0) :
    (environmentLaw μ).real {ω : Environment |
      t ≤ |pathWeight ω p - ∫ η : Environment, pathWeight η p ∂environmentLaw μ|} = 0 := by
  simpa only [pathWeight] using
    measure_abs_sum_sub_integral_ge_eq_zero_of_card_eq_zero
      (μ := environmentLaw μ)
      (fun (i : Fin (d.1 + d.2)) (ω : Environment) => ω (p.vertex i.castSucc))
      ht (by simpa only [Fintype.card_fin] using hd)

/-- A zero marginal bound gives no positive centered deviation on any fixed path. -/
theorem measure_abs_pathWeight_sub_integral_ge_eq_zero_of_bound_zero
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t)
    (hb : ∀ᵐ x ∂μ, |x| ≤ 0) {u : Lattice} {d : ℕ × ℕ} (p : Path u d) :
    (environmentLaw μ).real {ω : Environment |
      t ≤ |pathWeight ω p - ∫ η : Environment, pathWeight η p ∂environmentLaw μ|} = 0 := by
  simpa only [pathWeight] using
    measure_abs_sum_sub_integral_ge_eq_zero_of_bound_zero
      (μ := environmentLaw μ)
      (fun (i : Fin (d.1 + d.2)) (ω : Environment) => ω (p.vertex i.castSucc)) ht
      (ae_abs_path_collected_eval_le μ hb p)

end LPPDifferentiability
