/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.LastPassage.Bounds
public import LPP_Foundations.Probability.PassageIntegrable

import LPP_Foundations.Model.Paths.HorizontalFirst

/-!
# Finite passage means under integrable and bounded marginals

A deterministic path gives a lower bound on the finite passage mean whenever
the marginal has a genuine first moment. If the marginal weights are almost
surely bounded, this module derives integrability and bounds both the absolute
passage mean and the absolute value of its mean.
-/

@[expose] public section

open MeasureTheory

namespace LPPDifferentiability

/-- A deterministic horizontal-first path gives the finite passage lower bound. -/
theorem integral_lastPassage_ge_path_mean (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) (u : Lattice) (d : ℕ × ℕ) :
    ((d.1 + d.2 : ℕ) : ℝ) * ∫ x : ℝ, x ∂μ ≤
      ∫ ω : Environment, lastPassage ω u d ∂environmentLaw μ := by
  let p : Path u d := horizontalFirst u d
  have hp_int := integrable_pathWeight μ hμ p
  have hpass_int := integrable_lastPassage μ hμ u d
  calc
    ((d.1 + d.2 : ℕ) : ℝ) * ∫ x : ℝ, x ∂μ =
        ∫ ω : Environment, pathWeight ω p ∂environmentLaw μ :=
        (integral_pathWeight μ hμ p).symm
    _ ≤ ∫ ω : Environment, lastPassage ω u d ∂environmentLaw μ :=
      integral_mono hp_int hpass_int (fun ω => pathWeight_le_lastPassage ω p)

/-- An almost surely bounded real marginal has a genuine first moment. -/
theorem integrable_id_of_ae_abs_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (L : ℝ) (hμ : ∀ᵐ x ∂μ, |x| ≤ L) :
    Integrable (fun x : ℝ => x) μ := by
  refine (integrable_const L).mono' (by fun_prop) ?_
  filter_upwards [hμ] with x hx
  simpa only [Real.norm_eq_abs] using hx

/-- An almost surely bounded marginal makes every finite passage integrable. -/
theorem integrable_lastPassage_of_ae_abs_le (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (L : ℝ) (hμ : ∀ᵐ x ∂μ, |x| ≤ L)
    (u : Lattice) (d : ℕ × ℕ) :
    Integrable (fun ω : Environment => lastPassage ω u d) (environmentLaw μ) :=
  integrable_lastPassage μ (integrable_id_of_ae_abs_le μ L hμ) u d

/-- An almost surely bounded marginal bounds the mean absolute finite passage. -/
theorem integral_abs_lastPassage_le_of_ae_abs_le (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (L : ℝ) (_hL : 0 ≤ L)
    (hμ : ∀ᵐ x ∂μ, |x| ≤ L) (u : Lattice) (d : ℕ × ℕ) :
    ∫ ω : Environment, |lastPassage ω u d| ∂environmentLaw μ ≤
      ((d.1 + d.2 : ℕ) : ℝ) * L := by
  classical
  have hcoords : ∀ᵐ ω ∂environmentLaw μ, ∀ z : Lattice, |ω z| ≤ L := by
    rw [ae_all_iff]
    intro z
    have hmap : ∀ᵐ x ∂(environmentLaw μ).map (fun ω : Environment => ω z),
        |x| ≤ L := by
      rw [environmentLaw_map_eval]
      exact hμ
    exact ae_of_ae_map (measurable_environment_eval z).aemeasurable hmap
  have hpass_int := integrable_lastPassage_of_ae_abs_le μ L hμ u d
  have hpass_bound :
      (fun ω : Environment => |lastPassage ω u d|) ≤ᵐ[environmentLaw μ]
        (fun _ : Environment => ((d.1 + d.2 : ℕ) : ℝ) * L) := by
    filter_upwards [hcoords] with ω hω
    exact lastPassage_abs_le ω u d L hω
  have habs_int := hpass_int.abs
  have hconst_int : Integrable
      (fun _ : Environment => ((d.1 + d.2 : ℕ) : ℝ) * L) (environmentLaw μ) :=
    integrable_const _
  calc
    ∫ ω : Environment, |lastPassage ω u d| ∂environmentLaw μ ≤
        ∫ ω : Environment, ((d.1 + d.2 : ℕ) : ℝ) * L ∂environmentLaw μ :=
      integral_mono_ae habs_int hconst_int hpass_bound
    _ = ((d.1 + d.2 : ℕ) : ℝ) * L := by simp

/-- The absolute value of the finite passage mean obeys the same bounded-law estimate. -/
theorem abs_integral_lastPassage_le_of_ae_abs_le (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (L : ℝ) (hL : 0 ≤ L)
    (hμ : ∀ᵐ x ∂μ, |x| ≤ L) (u : Lattice) (d : ℕ × ℕ) :
    |∫ ω : Environment, lastPassage ω u d ∂environmentLaw μ| ≤
      ((d.1 + d.2 : ℕ) : ℝ) * L := by
  have hpass_int := integrable_lastPassage_of_ae_abs_le μ L hμ u d
  calc
    |∫ ω : Environment, lastPassage ω u d ∂environmentLaw μ| ≤
        ∫ ω : Environment, |lastPassage ω u d| ∂environmentLaw μ :=
      abs_integral_le_integral_abs
    _ ≤ ((d.1 + d.2 : ℕ) : ℝ) * L :=
      integral_abs_lastPassage_le_of_ae_abs_le μ L hL hμ u d

end LPPDifferentiability
