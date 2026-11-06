/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.UniformIncrementLaw
import Mathlib.Tactic.Linarith

/-! # Cumulative increments and the origin-column law

The sequence maps used in Liggett (1985), equation (2.14).
Coordinate zero represents length one; no diagonal array entry is used.
-/

public section

open MeasureTheory BoundedContinuousFunction

namespace LPPDifferentiability

/-- Cumulative sums through the positive length `k+1`. -/
@[expose] def sequencePartialSums (z : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), z j

theorem continuous_sequencePartialSums : Continuous sequencePartialSums :=
  continuous_pi fun k => continuous_finsetSum (Finset.range (k + 1)) fun j _ => continuous_apply j

theorem monotone_sequencePartialSums : Monotone sequencePartialSums := by
  intro x y hxy k
  exact Finset.sum_le_sum fun j _ => hxy j

private theorem sum_differences (a : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n, (a (j + 1) - a j)) = a n - a 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring

/-- Cumulative successive differences telescope at the positive origin. -/
theorem sequencePartialSums_originIncrementSequence {Ω : Type*}
    (X : ℕ → Ω → ℝ) (j : ℕ) (ω : Ω) (k : ℕ) :
    sequencePartialSums (originIncrementSequence X j ω) k =
      X (k + j + 2) ω - X (j + 1) ω := by
  have hindex (i : ℕ) : i + 1 + j + 1 = i + j + 2 := by omega
  simpa only [sequencePartialSums, originIncrementSequence, hindex, Nat.zero_add] using
    sum_differences (fun i => X (i + j + 1) ω) (k + 1)

/-- The probability law of cumulative sums of a real sequence. -/
@[expose] noncomputable def partialSumsLaw (ν : ProbabilityMeasure (ℕ → ℝ)) :
    ProbabilityMeasure (ℕ → ℝ) := ν.map sequencePartialSums

theorem partialSumsLaw_toMeasure (ν : ProbabilityMeasure (ℕ → ℝ)) :
    (partialSumsLaw ν : Measure (ℕ → ℝ)) = (ν : Measure (ℕ → ℝ)).map sequencePartialSums :=
  rfl

theorem measurable_originColumn {Ω : Type*} [MeasurableSpace Ω]
    (A : ℕ → ℕ → Ω → ℝ) (hm : ∀ j, 0 < j → Measurable (A 0 j)) :
    Measurable (fun ω => fun k : ℕ => A 0 (k + 1) ω) :=
  Measurable.of_eval fun k => hm _ (by omega)

/-- The law of the positive-length origin column. -/
@[expose] noncomputable def originColumnLaw {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : ℕ → ℕ → Ω → ℝ)
    (hm : ∀ j, 0 < j → Measurable (A 0 j)) : ProbabilityMeasure (ℕ → ℝ) :=
  ⟨μ.map (fun ω => fun k : ℕ => A 0 (k + 1) ω),
    (Measure.isProbabilityMeasure_map_iff (measurable_originColumn A hm).aemeasurable).2
      inferInstance⟩

theorem originColumnLaw_toMeasure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : ℕ → ℕ → Ω → ℝ)
    (hm : ∀ j, 0 < j → Measurable (A 0 j)) :
    (originColumnLaw μ A hm : Measure (ℕ → ℝ)) =
      μ.map (fun ω => fun k : ℕ => A 0 (k + 1) ω) := rfl

end LPPDifferentiability
