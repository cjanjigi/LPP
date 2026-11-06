/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Summable tails of integrable variables

Count the integer thresholds below each value and apply Tonelli.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace LPPDifferentiability

private theorem tsum_tail_indicator_le (a : ℝ) (ha : 0 ≤ a) :
    (∑' n : ℕ, {n : ℕ | (n : ℝ) < a}.indicator (fun _ => (1 : ℝ≥0∞)) n) ≤
      ENNReal.ofReal (a + 1) := by
  classical
  calc
    _ = ∑ n ∈ Finset.range (⌊a⌋₊ + 1),
        {n : ℕ | (n : ℝ) < a}.indicator (fun _ => (1 : ℝ≥0∞)) n := by
      apply tsum_eq_sum
      intro n hn
      have hfloor : ⌊a⌋₊ < n := by
        simp only [Finset.mem_range, not_lt] at hn
        omega
      have hnot : n ∉ {n : ℕ | (n : ℝ) < a} :=
        not_lt.mpr (Nat.lt_of_floor_lt hfloor).le
      exact Set.indicator_of_notMem hnot _
    _ ≤ ∑ _n ∈ Finset.range (⌊a⌋₊ + 1), (1 : ℝ≥0∞) := by
      exact Finset.sum_le_sum fun n _ => indicator_le_self _ _ _
    _ = ENNReal.ofReal ((⌊a⌋₊ : ℝ) + 1) := by
      rw [ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one]
      simp
    _ ≤ ENNReal.ofReal (a + 1) := ENNReal.ofReal_le_ofReal (add_le_add (Nat.floor_le ha) (le_refl (1 : ℝ)))

/-- The integer-threshold tails of a nonnegative integrable real variable have a
finite sum. -/
theorem integrable_nat_tails {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {g : Ω → ℝ}
    (hg : Integrable g μ) (hgnonneg : ∀ ω, 0 ≤ g ω) :
    (∑' n : ℕ, μ {ω | (n : ℝ) < g ω}) ≠ ∞ := by
  have hm (n : ℕ) : NullMeasurableSet {ω | (n : ℝ) < g ω} μ :=
    nullMeasurableSet_lt aemeasurable_const hg.aestronglyMeasurable.aemeasurable
  have hi : (∫⁻ ω, ENNReal.ofReal (g ω + 1) ∂μ) < ∞ := by
    exact (hasFiniteIntegral_iff_ofReal (ae_of_all μ (fun ω => by
      exact add_nonneg (hgnonneg ω) zero_le_one))).mp
        (hg.add (integrable_const 1)).hasFiniteIntegral
  apply ne_top_of_le_ne_top hi.ne
  calc
    _ = ∫⁻ ω, ∑' n : ℕ, {ω | (n : ℝ) < g ω}.indicator (fun _ => (1 : ℝ≥0∞)) ω ∂μ := by
      rw [lintegral_tsum (fun n => aemeasurable_const.indicator₀ (hm n))]
      congr 1
      funext n
      rw [lintegral_indicator_const₀ (hm n), one_mul]
    _ ≤ ∫⁻ ω, ENNReal.ofReal (g ω + 1) ∂μ := by
      apply lintegral_mono
      intro ω
      exact tsum_tail_indicator_le (g ω) (hgnonneg ω)

end LPPDifferentiability
