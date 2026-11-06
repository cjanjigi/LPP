/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.FiniteProductBoundedDifferences
public import ProbabilityBasics.Probability.BoundedSumConcentration
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Concentration on heterogeneous finite products

These are general consequences for functions on a finite product of probability spaces. Applying
them to a last-passage maximum still requires the identities between the model and the law, and
verifying each bounded-difference hypothesis.
-/

public section

open MeasureTheory ProbabilityTheory

namespace LPPDifferentiability

variable {n : ℕ} {E : Fin n → Type*} [∀ i, MeasurableSpace (E i)]
    (μ : ∀ i, Measure (E i)) [∀ i, IsProbabilityMeasure (μ i)]
    {F : (∀ i, E i) → ℝ} {M b : ℝ}

/-- Bounded coordinate differences give a sub-Gaussian bound for the centered function. -/
theorem hasSubgaussianMGF_centered_pi (hM : 0 ≤ M) (hb : 0 ≤ b)
    (hF : Measurable F) (hbound : ∀ x, |F x| ≤ M)
    (hosc : ∀ x i y, |F (Function.update x i y) - F x| ≤ b) :
    HasSubgaussianMGF (fun x => F x - ∫ z, F z ∂Measure.pi μ)
      (⟨(n : ℝ) * b ^ 2, mul_nonneg (Nat.cast_nonneg n) (sq_nonneg b)⟩ : NNReal)
      (Measure.pi μ) := by
  have hmean : |∫ z, F z ∂Measure.pi μ| ≤ M := by
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
      norm_integral_le_of_norm_le_const (μ := Measure.pi μ) (f := F) (C := M)
        (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hbound x)
  have hcenter : ∀ x, |F x - ∫ z, F z ∂Measure.pi μ| ≤ 2 * M := by
    intro x
    calc
      _ ≤ |F x| + |∫ z, F z ∂Measure.pi μ| := abs_sub _ _
      _ ≤ M + M := add_le_add (hbound x) hmean
      _ = 2 * M := by ring
  refine ⟨?_, ?_⟩
  · intro t
    exact integrable_exp_mul_of_mem_Icc (hF.sub_const _).aemeasurable
      (ae_of_all _ fun x => abs_le.mp (hcenter x))
  · intro t
    exact integral_exp_centered_pi_le μ hM hb hF hbound hosc t

/-- The two centered tails on a finite product, with parameter n*b². -/
theorem measure_abs_centered_pi_ge_le (hM : 0 ≤ M) (hb : 0 ≤ b)
    (hF : Measurable F) (hbound : ∀ x, |F x| ≤ M)
    (hosc : ∀ x i y, |F (Function.update x i y) - F x| ≤ b)
    {u : ℝ} (hu : 0 ≤ u) :
    (Measure.pi μ).real {x | u ≤ |F x - ∫ z, F z ∂Measure.pi μ|} ≤
      2 * Real.exp (-u ^ 2 / (2 * (n : ℝ) * b ^ 2)) := by
  have h := measure_abs_ge_le_of_hasSubgaussianMGF
    (hasSubgaussianMGF_centered_pi μ hM hb hF hbound hosc) hu
  change (Measure.pi μ).real {x | u ≤ |F x - ∫ z, F z ∂Measure.pi μ|} ≤
    2 * Real.exp (-u ^ 2 / (2 * ((n : ℝ) * b ^ 2))) at h
  simpa only [mul_assoc] using h

/-- With coordinate oscillation 2L, the denominator is exactly 8*n*L². -/
theorem measure_abs_centered_pi_ge_le_of_oscillation_two_mul
    {L : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hF : Measurable F) (hbound : ∀ x, |F x| ≤ M)
    (hosc : ∀ x i y, |F (Function.update x i y) - F x| ≤ 2 * L)
    {u : ℝ} (hu : 0 ≤ u) :
    (Measure.pi μ).real {x | u ≤ |F x - ∫ z, F z ∂Measure.pi μ|} ≤
      2 * Real.exp (-u ^ 2 / (8 * (n : ℝ) * L ^ 2)) := by
  have h := measure_abs_centered_pi_ge_le μ hM (mul_nonneg (by norm_num) hL)
    hF hbound hosc hu
  have hd : 2 * (n : ℝ) * (2 * L) ^ 2 = 8 * (n : ℝ) * L ^ 2 := by ring
  rwa [hd] at h

end LPPDifferentiability
