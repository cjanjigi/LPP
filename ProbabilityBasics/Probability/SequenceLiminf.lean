/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.IncrementPartialSums
public import ProbabilityBasics.Probability.SequenceAverages
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Order.LiminfLimsup

/-! # Extended-real lower limits of positive-length averages

Measurability and law pullbacks for the normalized lower limit in
Liggett's comparison. No finite-value or integrability assumption is made.
-/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace LPPDifferentiability

/-- The literal normalized extended-real lower limit of a measurable sequence
of real functions is measurable, including at infinite values. -/
theorem measurable_normalized_liminf {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (hm : ∀ j, Measurable (X j)) :
    Measurable (fun ω => liminf (fun j => ((X j ω / (j + 1) : ℝ) : EReal)) atTop) :=
  Measurable.liminf fun j => ((hm j).div_const (j + 1)).coe_real_ereal

/-- Closed real upper-threshold events of the genuine normalized lower limit
are measurable. -/
theorem measurableSet_normalized_liminf_ge (a : ℝ) :
    MeasurableSet {z : ℕ → ℝ | (a : EReal) ≤
      liminf (fun j => ((z j / (j + 1) : ℝ) : EReal)) atTop} :=
  measurableSet_le measurable_const
    (measurable_normalized_liminf (fun (j : ℕ) (z : ℕ → ℝ) => z j) measurable_pi_apply)

/-- The partial-sum lower limit is the real Birkhoff limit when the actual
coordinate averages converge. The identity uses positive lengths only. -/
theorem normalized_liminf_sequencePartialSums_eq_of_tendsto
    (z : ℕ → ℝ) (y : ℝ)
    (hy : Tendsto (fun n => birkhoffAverage ℝ sequenceShift
      (fun x : ℕ → ℝ => x 0) n z) atTop (𝓝 y)) :
    liminf (fun j => ((sequencePartialSums z j / (j + 1) : ℝ) : EReal)) atTop =
      (y : EReal) := by
  have hpos := hy.comp (tendsto_add_atTop_nat 1)
  have hid (j : ℕ) : birkhoffAverage ℝ sequenceShift
      (fun x : ℕ → ℝ => x 0) (j + 1) z = sequencePartialSums z j / (j + 1) := by
    rw [birkhoffAverage_sequenceShift_eval_zero]
    simp only [sequencePartialSums, Nat.cast_add, Nat.cast_one]
  simp only [Function.comp_def, hid] at hpos
  exact ((continuous_coe_real_ereal.tendsto y).comp hpos).liminf_eq

/-- Pull the actual cumulative-sum law's lower-limit event back to its
sequence probability space. -/
theorem measure_partialSumsLaw_normalized_liminf
    (κ : ProbabilityMeasure (ℕ → ℝ)) (a : ℝ) :
    (partialSumsLaw κ : Measure (ℕ → ℝ)) {z | (a : EReal) ≤
      liminf (fun j => ((z j / (j + 1) : ℝ) : EReal)) atTop} =
    (κ : Measure (ℕ → ℝ)) {z | (a : EReal) ≤
      liminf (fun j => ((sequencePartialSums z j / (j + 1) : ℝ) : EReal)) atTop} := by
  rw [partialSumsLaw_toMeasure,
    Measure.map_apply continuous_sequencePartialSums.measurable
      (measurableSet_normalized_liminf_ge a)]
  rfl

/-- Pull the actual origin-column law's event back to the original array
space. Diagonal and off-domain entries are unused. -/
theorem measure_originColumnLaw_normalized_liminf
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ℕ → ℕ → Ω → ℝ) (hm : ∀ j, 0 < j → Measurable (A 0 j)) (a : ℝ) :
    (originColumnLaw μ A hm : Measure (ℕ → ℝ)) {z | (a : EReal) ≤
      liminf (fun j => ((z j / (j + 1) : ℝ) : EReal)) atTop} =
    μ {ω | (a : EReal) ≤
      liminf (fun j => ((A 0 (j + 1) ω / (j + 1) : ℝ) : EReal)) atTop} := by
  rw [originColumnLaw_toMeasure,
    Measure.map_apply (measurable_originColumn A hm)
      (measurableSet_normalized_liminf_ge a)]
  rfl

end LPPDifferentiability
