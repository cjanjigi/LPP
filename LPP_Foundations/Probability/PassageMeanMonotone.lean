/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Probability.PassageLaw
public import LPP_Foundations.Probability.PassageMeanBounds

import Mathlib.Tactic

/-!
# Monotonicity of corrected finite passage means

For coordinatewise ordered natural endpoints, finite expected passage grows
by at least the mean of one fixed path across the displacement. Subtracting
the total displacement times the marginal mean therefore gives a monotone
quantity, with no sign assumption on the weights or their mean.
-/

public section

open MeasureTheory

namespace LPPDifferentiability

/-- The expected passage to a larger endpoint gains at least the marginal
mean times the added path length. -/
theorem integral_lastPassage_add_displacement_mean_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) (d e : ℕ × ℕ)
    (hd₁ : d.1 ≤ e.1) (hd₂ : d.2 ≤ e.2) :
    (∫ ω : Environment, lastPassage ω 0 d ∂environmentLaw μ) +
      (((e.1 - d.1) + (e.2 - d.2) : ℕ) : ℝ) * (∫ x : ℝ, x ∂μ) ≤
    ∫ ω : Environment, lastPassage ω 0 e ∂environmentLaw μ := by
  let δ : ℕ × ℕ := (e.1 - d.1, e.2 - d.2)
  have hdelta : d + δ = e := by
    apply Prod.ext
    · change d.1 + (e.1 - d.1) = e.1
      exact Nat.add_sub_of_le hd₁
    · change d.2 + (e.2 - d.2) = e.2
      exact Nat.add_sub_of_le hd₂
  have hsuper := integral_lastPassage_superadditive μ hμ 0 d δ
  rw [hdelta] at hsuper
  have hpath :
      (((e.1 - d.1) + (e.2 - d.2) : ℕ) : ℝ) * (∫ x : ℝ, x ∂μ) ≤
        ∫ ω : Environment, lastPassage ω 0 δ ∂environmentLaw μ := by
    simpa only [δ] using integral_lastPassage_ge_path_mean μ hμ 0 δ
  calc
    _ ≤ (∫ ω : Environment, lastPassage ω 0 d ∂environmentLaw μ) +
        (∫ ω : Environment, lastPassage ω 0 δ ∂environmentLaw μ) :=
      add_le_add le_rfl hpath
    _ ≤ ∫ ω : Environment, lastPassage ω 0 e ∂environmentLaw μ := hsuper

/-- Subtracting endpoint length times the marginal mean makes the expected
finite passage monotone under coordinatewise endpoint order. -/
theorem integral_lastPassage_corrected_monotone
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) (d e : ℕ × ℕ)
    (hd₁ : d.1 ≤ e.1) (hd₂ : d.2 ≤ e.2) :
    (∫ ω : Environment, lastPassage ω 0 d ∂environmentLaw μ) -
        ((d.1 + d.2 : ℕ) : ℝ) * (∫ x : ℝ, x ∂μ) ≤
    (∫ ω : Environment, lastPassage ω 0 e ∂environmentLaw μ) -
        ((e.1 + e.2 : ℕ) : ℝ) * (∫ x : ℝ, x ∂μ) := by
  let δ : ℕ × ℕ := (e.1 - d.1, e.2 - d.2)
  have hraw := integral_lastPassage_add_displacement_mean_le μ hμ d e hd₁ hd₂
  have hlenNat :
      (d.1 + d.2) + (δ.1 + δ.2) = e.1 + e.2 := by
    dsimp [δ]
    omega
  have hlen :
      ((d.1 + d.2 : ℕ) : ℝ) + ((δ.1 + δ.2 : ℕ) : ℝ) =
        ((e.1 + e.2 : ℕ) : ℝ) := by
    exact_mod_cast hlenNat
  have hcoeff :
      ((d.1 + d.2 : ℕ) : ℝ) * (∫ x : ℝ, x ∂μ) +
        ((δ.1 + δ.2 : ℕ) : ℝ) * (∫ x : ℝ, x ∂μ) =
      ((e.1 + e.2 : ℕ) : ℝ) * (∫ x : ℝ, x ∂μ) := by
    calc
      _ = (((d.1 + d.2 : ℕ) : ℝ) + ((δ.1 + δ.2 : ℕ) : ℝ)) *
          (∫ x : ℝ, x ∂μ) := by ring
      _ = _ := congrArg (fun n : ℝ => n * (∫ x : ℝ, x ∂μ)) hlen
  have hdeltaLen :
      ((δ.1 + δ.2 : ℕ) : ℝ) =
        (((e.1 - d.1) + (e.2 - d.2) : ℕ) : ℝ) := by
    rfl
  rw [← hdeltaLen] at hcoeff
  linarith only [hraw, hcoeff]

end LPPDifferentiability
