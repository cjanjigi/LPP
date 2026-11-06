/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.MartinBoundedContinuity
public import LPP_Foundations.Probability.PassageMeanMonotone
public import Martin2004.Analysis.FiniteQuadrantGrid
public import Mathlib.Topology.Order.LiminfLimsup

import Mathlib.Tactic

/-! # Uniform bounded expected passage approximation

Martin's finite lower-grid proof applies to the same actual continuous
expected rate, including signed bounded laws and the closed faces.
-/

public section

open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal NNRat

namespace LPPDifferentiability

/-- The actual positive integer-ray supremum bounds every finite passage
mean above by the same real expected rate at the natural endpoint. -/
theorem integral_lastPassage_le_real_expected_rate_of_ae_abs_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (L : ℝ) (hL : 0 ≤ L)
    (hμ : ∀ᵐ x ∂μ, |x| ≤ L) (g : Quadrant → ℝ)
    (hlim : ∀ x : Quadrant, Tendsto (fun n : ℕ =>
      (∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
        ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (g x)))
    (z : ℕ × ℕ) :
    (∫ ω : Environment, lastPassage ω 0 z ∂environmentLaw μ) ≤
      g ((z.1 : ℝ≥0), (z.2 : ℝ≥0)) := by
  obtain ⟨G, ⟨hG, _⟩, _⟩ :=
    exists_unique_lastPassage_natural_shape_of_ae_abs_le μ L hL hμ
  have hagree := real_expected_rate_agrees_natural μ g hlim G
    (fun a => (hG.1 a).1)
  rw [hagree z, (hG.1 z).2.1]
  have hb := ((hG.1 z).1.comp (tendsto_add_atTop_nat 1)).bddAbove_range
  have hm := le_csSup hb (mem_range_self 0)
  simpa only [Function.comp_def, Nat.zero_add, Nat.cast_one, one_smul, div_one] using hm

/-- A bounded marginal law determines the same unique actual continuous
expected rate with its entire parent characterization, its finite lattice
upper bound, and uniform expected approximation at every sufficiently long
natural endpoint. The only premises are probability and the bounded law. -/
theorem exists_unique_uniform_lastPassage_real_expected_rate_of_ae_abs_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (L : ℝ) (hL : 0 ≤ L)
    (hμ : ∀ᵐ x ∂μ, |x| ≤ L) :
    ∃! g : Quadrant → ℝ,
      (
      (
      ((∀ x : Quadrant, Tendsto (fun n : ℕ =>
        (∫ ω : Environment, lastPassage ω 0
          (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
          ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (g x))) ∧
      Continuous (fun x : QuadrantInterior => g x.val) ∧
      g 0 = 0 ∧
      (∀ s : ℝ≥0, g (s, 0) = (∫ t : ℝ, t ∂μ) * (s : ℝ)) ∧
      (∀ t : ℝ≥0, g (0, t) = (∫ s : ℝ, s ∂μ) * (t : ℝ)) ∧
      (∃ F : (ℚ≥0 × ℚ≥0) → ℝ,
        (∀ q : ℚ≥0 × ℚ≥0, Tendsto (fun n : ℕ =>
          (∫ ω : Environment, lastPassage ω 0
            (⌊(n : ℝ) * (q.1 : ℝ)⌋₊, ⌊(n : ℝ) * (q.2 : ℝ)⌋₊)
            ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (F q))) ∧
        (∀ q : ℚ≥0 × ℚ≥0, g (nnratPairToQuadrant q) = F q)) ∧
      (∀ z : ℕ × ℕ, Integrable (fun ω : Environment => lastPassage ω 0 z)
        (environmentLaw μ))) ∧
      (∀ (c : ℝ≥0) (x : Quadrant), g (c • x) = (c : ℝ) * g x) ∧
      (∀ x y : Quadrant, g x + g y ≤ g (x + y)) ∧
      (∀ x : Quadrant, g x.swap = g x) ∧
      (∀ (L : ℝ), 0 ≤ L → (∀ᵐ t ∂μ, |t| ≤ L) →
        ∀ x : Quadrant, |g x| ≤ L * ((x.1 : ℝ) + x.2))) ∧
      Continuous g ∧
      (∀ h t : ℝ≥0,
        |g (h, t) - (t : ℝ) * (∫ x : ℝ, x ∂μ)| ≤
          (h : ℝ) * L + 8 * L * Real.sqrt (((h : ℝ) + t) *
            (((h : ℝ) + t) * Real.log ((h : ℝ) + t) -
              (h : ℝ) * Real.log h - (t : ℝ) * Real.log t))) ∧
      (∀ R ε : ℝ, 0 < R → 0 < ε →
        ∃ δ : ℝ≥0, 0 < δ ∧ ∀ h : ℝ≥0, h ≤ δ → ∀ t : ℝ≥0,
          (t : ℝ) ≤ R →
            |g (h, t) - g (0, t)| < ε ∧ |g (t, h) - g (t, 0)| < ε)) ∧
      (∀ z : ℕ × ℕ,
        (∫ ω : Environment, lastPassage ω 0 z ∂environmentLaw μ) ≤
          g ((z.1 : ℝ≥0), (z.2 : ℝ≥0))) ∧
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 0 < N ∧ ∀ z : ℕ × ℕ,
        N ≤ z.1 + z.2 →
        |(∫ ω : Environment, lastPassage ω 0 z ∂environmentLaw μ) -
          g ((z.1 : ℝ≥0), (z.2 : ℝ≥0))| <
            ε * ((z.1 + z.2 : ℕ) : ℝ)) := by
  obtain ⟨g, hg, hUnique⟩ :=
    exists_unique_continuous_lastPassage_real_expected_rate_of_ae_abs_le μ L hL hμ
  have hupper := integral_lastPassage_le_real_expected_rate_of_ae_abs_le
    μ L hL hμ g hg.1.1.1
  have hstep (d z : ℕ × ℕ) (hd₁ : d.1 ≤ z.1) (hd₂ : d.2 ≤ z.2) :
      (∫ ω : Environment, lastPassage ω 0 d ∂environmentLaw μ) -
        L * (((z.1 - d.1) + (z.2 - d.2) : ℕ) : ℝ) ≤
      ∫ ω : Environment, lastPassage ω 0 z ∂environmentLaw μ := by
    have hmean := (abs_le.mp (abs_integral_id_le_of_ae_abs_le μ L hL hμ)).1
    have hinc := integral_lastPassage_add_displacement_mean_le μ
      (integrable_id_of_ae_abs_le μ L hμ) d z hd₁ hd₂
    have hmul := mul_le_mul_of_nonneg_left hmean
      (Nat.cast_nonneg ((z.1 - d.1) + (z.2 - d.2)) :
        (0 : ℝ) ≤ (((z.1 - d.1) + (z.2 - d.2) : ℕ) : ℝ))
    nlinarith only [hinc, hmul]
  have huniform := uniform_lattice_approximation_of_finite_lower_grid
    (fun z => ∫ ω : Environment, lastPassage ω 0 z ∂environmentLaw μ)
    g L hL hstep hg.1.1.1 hg.2.1 hg.1.2.1 hupper
  refine ⟨g, ⟨hg, hupper, huniform⟩, ?_⟩
  intro f hf
  exact hUnique f hf.1

end LPPDifferentiability
