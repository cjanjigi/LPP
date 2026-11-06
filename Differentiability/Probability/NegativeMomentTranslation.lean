/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Translation preserves a finite negative-part moment

A finite negative-part moment of order greater than one remains finite at the
same order under every real translation of the actual probability law.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace LPPDifferentiability

private theorem negativePart_rpow_translation_bound
    (x c p : ℝ) (hp : 0 ≤ p) :
    ENNReal.ofReal ((max (-(x + c)) 0) ^ p) ≤
      (2 : ℝ≥0∞) ^ p *
        (ENNReal.ofReal ((max (-x) 0) ^ p) + ENNReal.ofReal (|c| ^ p)) := by
  have hshift : max (-(x + c)) 0 ≤ max (-x) 0 + |c| := by
    apply max_le
    · calc
        -(x + c) = -x + -c := by ring
        _ ≤ -x + |c| := add_le_add_right (neg_le_abs c) (-x)
        _ ≤ max (-x) 0 + |c| :=
          add_le_add_left (le_max_left (-x) 0) |c|
    · exact add_nonneg (le_max_right _ _) (abs_nonneg c)
  have hshiftENN :
      ENNReal.ofReal (max (-(x + c)) 0) ≤
        ENNReal.ofReal (max (-x) 0) + ENNReal.ofReal |c| := by
    rw [← ENNReal.ofReal_add (le_max_right _ _) (abs_nonneg c)]
    exact ENNReal.ofReal_le_ofReal hshift
  calc
    ENNReal.ofReal ((max (-(x + c)) 0) ^ p) =
        ENNReal.ofReal (max (-(x + c)) 0) ^ p := by
      symm
      exact ENNReal.ofReal_rpow_of_nonneg (le_max_right _ _) hp
    _ ≤ (ENNReal.ofReal (max (-x) 0) + ENNReal.ofReal |c|) ^ p :=
      ENNReal.rpow_le_rpow hshiftENN hp
    _ ≤ (2 : ℝ≥0∞) ^ p *
        (ENNReal.ofReal (max (-x) 0) ^ p + ENNReal.ofReal |c| ^ p) :=
      ENNReal.add_rpow_le_two_rpow_mul_rpow_add_rpow _ _ hp
    _ = (2 : ℝ≥0∞) ^ p *
        (ENNReal.ofReal ((max (-x) 0) ^ p) + ENNReal.ofReal (|c| ^ p)) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (le_max_right _ _) hp,
        ENNReal.ofReal_rpow_of_nonneg (abs_nonneg c) hp]

private theorem measurable_negativePart_rpow_integrand (p : ℝ) (hp : 0 ≤ p) :
    Measurable (fun x : ℝ => ENNReal.ofReal ((max (-x) 0) ^ p)) := by
  exact ENNReal.measurable_ofReal.comp
    ((continuous_id.neg.max continuous_const).rpow_const
      (fun _ => Or.inr hp)).measurable

/-- A finite negative-part moment above order one stays finite, at the same
order, under the actual law translated by any signed real constant. -/
theorem finite_lintegral_negativePart_rpow_map_add_of_lintegral_lt_top
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (p c : ℝ) (hp : 1 < p)
    (hmoment : (∫⁻ x, ENNReal.ofReal ((max (-x) 0) ^ p) ∂μ) < ∞) :
    (∫⁻ x, ENNReal.ofReal ((max (-x) 0) ^ p) ∂(μ.map (fun x => x + c))) < ∞ := by
  have hp0 : 0 ≤ p := le_trans zero_le_one hp.le
  let integrand : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal ((max (-x) 0) ^ p)
  let coefficient : ℝ≥0∞ := (2 : ℝ≥0∞) ^ p
  let constant : ℝ≥0∞ := ENNReal.ofReal (|c| ^ p)
  let majorant : ℝ → ℝ≥0∞ := fun x => integrand x + constant
  have hmeas : Measurable integrand :=
    measurable_negativePart_rpow_integrand p hp0
  have hmajorant_meas : Measurable majorant := hmeas.add measurable_const
  have hmoment' : (∫⁻ x, integrand x ∂μ) < ∞ := by
    simpa only [integrand] using hmoment
  have hcoefficient : coefficient < ∞ := by
    dsimp [coefficient]
    exact ENNReal.rpow_lt_top_of_nonneg hp0 ENNReal.coe_ne_top
  have hconstant : constant < ∞ := by
    dsimp [constant]
    exact ENNReal.ofReal_lt_top
  have hsum :
      (∫⁻ x, majorant x ∂μ) = (∫⁻ x, integrand x ∂μ) + constant := by
    dsimp [majorant]
    rw [lintegral_add_right (f := integrand) (g := fun _ => constant) measurable_const,
      lintegral_const, measure_univ, mul_one]
  have hmajor :
      (∫⁻ x, coefficient * (integrand x + constant) ∂μ) < ∞ := by
    calc
      (∫⁻ x, coefficient * (integrand x + constant) ∂μ) =
          ∫⁻ x, coefficient * majorant x ∂μ := by
        rfl
      _ = coefficient * (∫⁻ x, majorant x ∂μ) :=
        lintegral_const_mul coefficient hmajorant_meas
      _ = coefficient * ((∫⁻ x, integrand x ∂μ) + constant) := by rw [hsum]
      _ < ∞ := ENNReal.mul_lt_top hcoefficient
        (ENNReal.add_lt_top.mpr ⟨hmoment', hconstant⟩)
  rw [lintegral_map hmeas (by fun_prop)]
  apply lt_of_le_of_lt _ hmajor
  exact lintegral_mono fun x => by
    dsimp [integrand, coefficient, constant]
    exact negativePart_rpow_translation_bound x c p hp0

end LPPDifferentiability
