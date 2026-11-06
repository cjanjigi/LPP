/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.UniformOriginBounds
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.LiminfLimsup

/-!
# First moments of uniform-origin increments

These lemmas implement equations (2.11) and (2.12) of Liggett (1985). The
normalized expected-rate limit of equation (2.1) is an explicit intermediate
input. It is to be produced from the array assumptions before a final theorem
uses it.
-/

public section

open MeasureTheory ProbabilityTheory Filter Topology

namespace LPPDifferentiability

private theorem tendsto_shifted_difference (a : ℕ → ℝ) (γ : ℝ)
    (ha : Tendsto (fun n : ℕ => a (n + 1) / (n + 1 : ℝ)) atTop (𝓝 γ)) (k : ℕ) :
    Tendsto (fun n : ℕ => (a (k + n + 2) - a (k + 1)) / (n + 1 : ℝ)) atTop (𝓝 γ) := by
  have hs : Tendsto (fun n : ℕ => a (k + n + 2) / ((k + n + 2 : ℕ) : ℝ))
      atTop (𝓝 γ) := by
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.cast_add,
      Nat.cast_one, Nat.cast_ofNat, add_assoc, add_comm, add_left_comm, one_add_one_eq_two] using
      (tendsto_add_atTop_iff_nat (k + 1)).2 ha
  have hc (c : ℝ) : Tendsto (fun n : ℕ => c / (n + 1 : ℝ)) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_add_atTop_iff_nat 1).2 (tendsto_const_div_atTop_nhds_zero_nat c)
  have h := (hs.mul ((tendsto_const_nhds (x := (1 : ℝ))).add (hc (k + 1)))).sub
    (hc (a (k + 1)))
  simp only [add_zero, mul_one, sub_zero] at h
  convert h using 1
  funext n
  have h1 : (n + 1 : ℝ) ≠ 0 := by positivity
  have h2 : ((k + n + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  push_cast at h2 ⊢
  field_simp [h1, h2]
  ring

/-- Equation (2.12) of Liggett (1985) for the finite-product increments at every
fixed positive coordinate, using the expected-rate conclusion of equation (2.1). -/
theorem tendsto_integral_uniformOriginIncrement {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hm : ∀ j, 0 < j → Measurable (X j))
    (hi : ∀ j, 0 < j → Integrable (X j) μ) (γ : ℝ)
    (hγ : Tendsto (fun n : ℕ => (∫ ω, X (n + 1) ω ∂μ) / (n + 1 : ℝ)) atTop (𝓝 γ))
    (k : ℕ) :
    Tendsto (fun n => ∫ p, uniformOriginIncrement X n k p ∂uniformOriginProduct μ n)
      atTop (𝓝 γ) := by
  simp_rw [integral_uniformOriginIncrement μ X hm hi]
  exact tendsto_shifted_difference (fun j => ∫ ω, X j ω ∂μ) γ hγ k

/-- Integrating the elementary positive-part identity requires only the first
moment of each finite-product increment. -/
theorem integral_abs_uniformOriginIncrement_eq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hm : ∀ j, 0 < j → Measurable (X j))
    (hi : ∀ j, 0 < j → Integrable (X j) μ) (n k : ℕ) :
    (∫ p, |uniformOriginIncrement X n k p| ∂uniformOriginProduct μ n) =
      2 * (∫ p, max (uniformOriginIncrement X n k p) 0 ∂uniformOriginProduct μ n) -
        (∫ p, uniformOriginIncrement X n k p ∂uniformOriginProduct μ n) := by
  have hY := integrable_uniformOriginIncrement μ X hm hi n k
  have hpos : Integrable (fun p => max (uniformOriginIncrement X n k p) 0)
      (uniformOriginProduct μ n) := by
    simpa only [Pi.sup_def, Pi.zero_apply] using hY.sup (integrable_zero _ _ _)
  calc
    _ = ∫ p, (2 * max (uniformOriginIncrement X n k p) 0 -
        uniformOriginIncrement X n k p) ∂uniformOriginProduct μ n := by
      apply integral_congr_ae
      filter_upwards [] with p
      by_cases hp : 0 ≤ uniformOriginIncrement X n k p
      · rw [abs_of_nonneg hp, max_eq_left hp]
        ring
      · rw [abs_of_neg (lt_of_not_ge hp), max_eq_right (le_of_not_ge hp)]
        ring
    _ = _ := by rw [integral_sub (hpos.const_mul 2) hY, integral_const_mul]

/-- Equation (2.11) of Liggett (1985): for each positive coordinate, all finite
window sizes have a common finite first absolute moment bound. -/
theorem exists_integral_abs_uniformOriginIncrement_bound {Ω A : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure A)
    (X Z : ℕ → Ω → ℝ) (g : A → ℝ)
    (hdom : ∀ j, 0 < j → ∀ᵐ ω ∂μ, X (j + 1) ω - X j ω ≤ Z j ω)
    (hlaw : ∀ j, 0 < j → IdentDistrib (Z j) g μ ν)
    (hg : Integrable g ν) (hm : ∀ j, 0 < j → Measurable (X j))
    (hi : ∀ j, 0 < j → Integrable (X j) μ) (γ : ℝ)
    (hγ : Tendsto (fun n : ℕ => (∫ ω, X (n + 1) ω ∂μ) / (n + 1 : ℝ)) atTop (𝓝 γ))
    (k : ℕ) :
    ∃ C : ℝ, ∀ n, (∫ p, |uniformOriginIncrement X n k p| ∂uniformOriginProduct μ n) ≤ C := by
  obtain ⟨L, hL⟩ := (tendsto_integral_uniformOriginIncrement μ X hm hi γ hγ k).bddBelow_range
  refine ⟨2 * (∫ a, max (g a) 0 ∂ν) - L, fun n => ?_⟩
  rw [integral_abs_uniformOriginIncrement_eq μ X hm hi n k]
  have hp := integral_uniformOriginIncrement_pos_le μ ν X Z g hdom hlaw hg hm hi n k
  have hl := hL (Set.mem_range_self n)
  linarith only [hp, hl]

end LPPDifferentiability
