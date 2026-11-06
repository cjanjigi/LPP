/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.WeakMoment

/-!
# First moments of weak limits

A convergent sequence of finite nonnegative means bounds the mean of its weak
limit from above. This is a consequence of the bounded first-moment helper:
each strict upper bound on the limiting means holds eventually, and shifting
past the finite exceptional prefix makes it a common bound.
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace LPPDifferentiability

private theorem integrable_nonneg_of_weak_integral_eventually_le
    (μ : ℕ → ProbabilityMeasure ℝ) (ν : ProbabilityMeasure ℝ)
    (hweak : Tendsto μ atTop (𝓝 ν)) (g : ℝ → ℝ) (hg : Continuous g)
    (hg0 : ∀ x, 0 ≤ g x) (hgi : ∀ n, Integrable g (μ n : Measure ℝ))
    (C : ℝ)
    (hbound : ∀ᶠ n in atTop, (∫ x, g x ∂(μ n : Measure ℝ)) ≤ C) :
    Integrable g (ν : Measure ℝ) ∧ (∫ x, g x ∂(ν : Measure ℝ)) ≤ C := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hbound
  let μN : ℕ → ProbabilityMeasure ℝ := fun n => μ (n + N)
  have hweakN : Tendsto μN atTop (𝓝 ν) := by
    change Tendsto (fun n => μ (n + N)) atTop (𝓝 ν)
    have hshift : Tendsto (fun n : ℕ => n + N) atTop atTop :=
      tendsto_atTop_mono (fun n => Nat.le_add_right n N) tendsto_id
    exact hweak.comp hshift
  have hboundN (n : ℕ) :
      (∫ x, g x ∂(μN n : Measure ℝ)) ≤ C := by
    change (∫ x, g x ∂(μ (n + N) : Measure ℝ)) ≤ C
    exact hN (n + N) (Nat.le_add_left N n)
  exact integrable_nonneg_of_weak_integral_le μN ν hweakN g hg hg0
    (fun n => hgi (n + N)) C hboundN

/-- If integrable means of a continuous nonnegative function converge to a
finite real number, then the function is integrable under the weak limit and
its mean is at most that limit. The mean may decrease in the weak limit. -/
theorem integrable_nonneg_of_weak_integral_tendsto_le
    (μ : ℕ → ProbabilityMeasure ℝ) (ν : ProbabilityMeasure ℝ)
    (hweak : Tendsto μ atTop (𝓝 ν)) (g : ℝ → ℝ) (hg : Continuous g)
    (hg0 : ∀ x, 0 ≤ g x) (hgi : ∀ n, Integrable g (μ n : Measure ℝ))
    (q : ℝ)
    (hmean : Tendsto (fun n => ∫ x, g x ∂(μ n : Measure ℝ)) atTop (𝓝 q)) :
    Integrable g (ν : Measure ℝ) ∧ (∫ x, g x ∂(ν : Measure ℝ)) ≤ q := by
  have hupper (C : ℝ) (hqC : q < C) :
      Integrable g (ν : Measure ℝ) ∧ (∫ x, g x ∂(ν : Measure ℝ)) ≤ C := by
    apply integrable_nonneg_of_weak_integral_eventually_le
      μ ν hweak g hg hg0 hgi C
    have hpositive : 0 < C - q := sub_pos.mpr hqC
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hmean (C - q) hpositive
    filter_upwards [eventually_ge_atTop N] with n hn
    have hdist := hN n hn
    rw [Real.dist_eq] at hdist
    have hright := (abs_lt.mp hdist).2
    linarith
  refine ⟨(hupper (q + 1) (by linarith)).1, ?_⟩
  apply le_of_forall_pos_le_add
  intro ε hε
  exact (hupper (q + ε) (by linarith)).2

end LPPDifferentiability
