/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.WeakNegativeShape
public import LPP_Foundations.Probability.PassageMeanBounds

import Mathlib.Analysis.SpecificLimits.Basic

/-! # The shape function lies above the mean weight

Under the weak negative moment and the positive integrated square-root tail,
the shape `g` satisfies `(x.1 + x.2) * E w_0 ≤ g x` at every point of the
closed quadrant. The proof compares the normalized expected passage times,
which converge to `g`, with the mean of a fixed path (the lower bound
`integral_lastPassage_ge_path_mean`).
-/

public section

open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

namespace LPPDifferentiability

/-- A consequence of the shape theorem: at every point of the closed quadrant, the shape is at
least the level times the mean weight. The function `g` has the four properties of the
weak-negative shape theorem. -/
theorem level_mul_integral_le_shape_of_negative_moment_and_positive_tail
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : ∃ p : ℝ, 1 < p ∧
      (∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ p) ∂μ) < ∞)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞)
    (g : Quadrant → ℝ) (hgc : Continuous g)
    (hgh : ∀ (c : ℝ≥0) (x : Quadrant),
      g (c * x.1, c * x.2) = (c : ℝ) * g x)
    (hgconc : ∀ (x y : Quadrant) (a b : ℝ≥0), a + b = 1 →
      (a : ℝ) * g x + (b : ℝ) * g y ≤
        g (a * x.1 + b * y.1, a * x.2 + b * y.2))
    (hgae : ∀ᵐ ω ∂environmentLaw μ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage ω 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ))
    (x : Quadrant) :
    ((x.1 : ℝ) + (x.2 : ℝ)) * ∫ t : ℝ, t ∂μ ≤ g x := by
  have hμ := integrable_id_of_negative_moment_and_positive_tail μ hneg hpos
  obtain ⟨g₀, _hg₀, hunique⟩ :=
    exists_unique_shape_of_negative_moment_and_positive_tail μ hneg hpos
  obtain ⟨g', hg', _hunique'⟩ :=
    exists_unique_shape_with_expected_rate_of_negative_moment_and_positive_tail μ hneg hpos
  have h1 : g = g₀ := hunique g ⟨hgc, hgh, hgconc, hgae⟩
  have h2 : g' = g₀ := hunique g' ⟨hg'.1, hg'.2.1, hg'.2.2.1, hg'.2.2.2.1⟩
  have hgg' : g = g' := h1.trans h2.symm
  have hexp := hg'.2.2.2.2.1 x
  rw [← hgg'] at hexp
  set m : ℝ := ∫ t : ℝ, t ∂μ with hm
  have hfloor : ∀ a : ℝ≥0, Tendsto (fun n : ℕ =>
      (⌊(n : ℝ) * (a : ℝ)⌋₊ : ℝ) / (n : ℝ)) atTop (𝓝 (a : ℝ)) := by
    intro a
    have h := (tendsto_nat_floor_mul_div_atTop (R := ℝ) (a := (a : ℝ)) a.2).comp
      tendsto_natCast_atTop_atTop
    refine h.congr fun n => ?_
    simp only [Function.comp_apply, mul_comm]
  have hlim : Tendsto (fun n : ℕ =>
      ((⌊(n : ℝ) * (x.1 : ℝ)⌋₊ : ℝ) / (n : ℝ) +
        (⌊(n : ℝ) * (x.2 : ℝ)⌋₊ : ℝ) / (n : ℝ)) * m) atTop
      (𝓝 (((x.1 : ℝ) + (x.2 : ℝ)) * m)) :=
    ((hfloor x.1).add (hfloor x.2)).mul_const m
  refine le_of_tendsto_of_tendsto' hlim hexp fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hpath := integral_lastPassage_ge_path_mean μ hμ 0
      (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
    rw [← hm] at hpath
    rw [← add_div, div_mul_eq_mul_div]
    refine div_le_div_of_nonneg_right ?_ hnR.le
    simpa only [Nat.cast_add] using hpath

/-- The direction form used for the flat-segment bound: for `a + b = 1`, the
shape at `(a, b)` is at least the mean weight. -/
theorem integral_le_shape_of_negative_moment_and_positive_tail
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : ∃ p : ℝ, 1 < p ∧
      (∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ p) ∂μ) < ∞)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞)
    (g : Quadrant → ℝ) (hgc : Continuous g)
    (hgh : ∀ (c : ℝ≥0) (x : Quadrant),
      g (c * x.1, c * x.2) = (c : ℝ) * g x)
    (hgconc : ∀ (x y : Quadrant) (a b : ℝ≥0), a + b = 1 →
      (a : ℝ) * g x + (b : ℝ) * g y ≤
        g (a * x.1 + b * y.1, a * x.2 + b * y.2))
    (hgae : ∀ᵐ ω ∂environmentLaw μ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage ω 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ))
    (a b : ℝ≥0) (hab : a + b = 1) :
    ∫ t : ℝ, t ∂μ ≤ g (a, b) := by
  have h := level_mul_integral_le_shape_of_negative_moment_and_positive_tail
    μ hneg hpos g hgc hgh hgconc hgae (a, b)
  have hab' : (a : ℝ) + (b : ℝ) = 1 := by exact_mod_cast hab
  simpa only [hab', one_mul] using h

end LPPDifferentiability
