/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Probability.PassageIntegrable
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# First moments from one-sided moment assumptions

Finite real-power moments of the positive and negative parts give a first moment in the sense of
the Bochner integral. The last three lemmas use the moment assumptions (A2) and (A3) of the
differentiability preprint. These results do not establish Martin's integrated tail
assumptions, a shape theorem, or differentiability.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace LPPDifferentiability

/-- A continuous nonnegative function with a finite moment of order at least one
is integrable under a finite measure. -/
theorem integrable_of_nonneg_rpow_lintegral_lt_top
    (μ : Measure ℝ) [IsFiniteMeasure μ] (f : ℝ → ℝ)
    (hf : Continuous f) (hnonneg : ∀ x, 0 ≤ f x)
    (p : ℝ) (hp : 1 ≤ p)
    (hmoment : (∫⁻ x, ENNReal.ofReal (f x ^ p) ∂μ) < ∞) :
    Integrable f μ := by
  have hp0 : 0 ≤ p := le_trans zero_le_one hp
  have hint : Integrable (fun x => f x ^ p) μ := by
    refine ⟨(hf.rpow_const (fun _ => Or.inr hp0)).aestronglyMeasurable, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall (fun x => Real.rpow_nonneg (hnonneg x) p))).2 hmoment
  have hnorm : Integrable (fun x => ‖f x‖ ^ p) μ := by
    have heq : (fun x => ‖f x‖ ^ p) = (fun x => f x ^ p) := by
      funext x
      rw [Real.norm_of_nonneg (hnonneg x)]
    rw [heq]
    exact hint
  have hfirst := integrable_norm_rpow_of_le hf.aestronglyMeasurable
    zero_le_one hp0 hp hnorm
  exact (integrable_norm_iff hf.aestronglyMeasurable).1
    (by simpa only [Real.rpow_one] using hfirst)

/-- Both one-sided moments of order greater than one suffice for the first moment. -/
theorem integrable_id_of_one_sided_moments
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : ∃ pneg : ℝ, 1 < pneg ∧
      (∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ pneg) ∂μ) < ∞)
    (hpos : ∃ ppos : ℝ, 1 < ppos ∧
      (∫⁻ t, ENNReal.ofReal ((max t 0) ^ ppos) ∂μ) < ∞) :
    Integrable (fun x : ℝ => x) μ := by
  obtain ⟨pneg, hpneg, hmomentneg⟩ := hneg
  obtain ⟨ppos, hppos, hmomentpos⟩ := hpos
  have hnegative : Integrable (fun t : ℝ => max (-t) 0) μ :=
    integrable_of_nonneg_rpow_lintegral_lt_top μ _
      (continuous_id.neg.max continuous_const) (fun _ => le_max_right _ _)
      pneg hpneg.le hmomentneg
  have hpositive : Integrable (fun t : ℝ => max t 0) μ :=
    integrable_of_nonneg_rpow_lintegral_lt_top μ _
      (continuous_id.max continuous_const) (fun _ => le_max_right _ _)
      ppos hppos.le hmomentpos
  have heq : (fun t : ℝ => max t 0 - max (-t) 0) = (fun t : ℝ => t) := by
    funext t
    rcases le_total 0 t with ht | ht
    · rw [max_eq_left ht, max_eq_right (neg_nonpos.mpr ht), sub_zero]
    · rw [max_eq_right ht, max_eq_left (neg_nonneg.mpr ht), zero_sub, neg_neg]
  rw [← heq]
  exact hpositive.sub hnegative

/-- Assumptions (A2) and (A3) of the differentiability preprint, with exponents
`1 < pneg` and `4 < ppos`, imply the first moment. -/
theorem integrable_id_of_paper_moments
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : ∃ pneg : ℝ, 1 < pneg ∧
      (∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ pneg) ∂μ) < ∞)
    (hpos : ∃ ppos : ℝ, 4 < ppos ∧
      (∫⁻ t, ENNReal.ofReal ((max t 0) ^ ppos) ∂μ) < ∞) :
    Integrable (fun x : ℝ => x) μ := by
  apply integrable_id_of_one_sided_moments μ hneg
  obtain ⟨ppos, hppos, hmoment⟩ := hpos
  exact ⟨ppos, lt_trans (by norm_num : (1 : ℝ) < 4) hppos, hmoment⟩

/-- Every path weight is integrable under the moment assumptions (A2) and (A3). -/
theorem integrable_pathWeight_of_paper_moments
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : ∃ pneg : ℝ, 1 < pneg ∧
      (∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ pneg) ∂μ) < ∞)
    (hpos : ∃ ppos : ℝ, 4 < ppos ∧
      (∫⁻ t, ENNReal.ofReal ((max t 0) ^ ppos) ∂μ) < ∞)
    {u : Lattice} {d : ℕ × ℕ} (p : Path u d) :
    Integrable (fun ω : Environment => pathWeight ω p) (environmentLaw μ) :=
  integrable_pathWeight μ (integrable_id_of_paper_moments μ hneg hpos) p

/-- The last-passage time is integrable under the moment assumptions (A2) and (A3). -/
theorem integrable_lastPassage_of_paper_moments
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : ∃ pneg : ℝ, 1 < pneg ∧
      (∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ pneg) ∂μ) < ∞)
    (hpos : ∃ ppos : ℝ, 4 < ppos ∧
      (∫⁻ t, ENNReal.ofReal ((max t 0) ^ ppos) ∂μ) < ∞)
    (u : Lattice) (d : ℕ × ℕ) :
    Integrable (fun ω : Environment => lastPassage ω u d) (environmentLaw μ) :=
  integrable_lastPassage μ (integrable_id_of_paper_moments μ hneg hpos) u d

end LPPDifferentiability
