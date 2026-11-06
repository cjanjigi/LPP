/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.MaximumQuantileGap

/-!
# The real quantile on the open unit interval

Scalar prerequisites for a later discretization argument. Atoms are
retained; no continuity, support or moment assumption is made on the law.
-/

public section

open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology

namespace LPPDifferentiability

/-- The inverse-CDF identity, with the real infimum. -/
theorem source_quantile_le_iff (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    sInf {s : ℝ | u ≤ μ.real (Iic s)} ≤ t ↔ u ≤ μ.real (Iic t) := by
  constructor
  · intro h
    by_contra ht
    exact (not_lt_of_ge h) (lt_source_quantile μ (lt_of_not_ge ht) hu.2)
  · intro ht
    exact csInf_le (source_quantile_set_bddBelow μ hu.1) ht

/-- Quantiles are monotone at levels strictly between zero and one. -/
theorem source_quantile_mono (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {u v : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (hv : v ∈ Ioo (0 : ℝ) 1)
    (huv : u ≤ v) :
    sInf {s : ℝ | u ≤ μ.real (Iic s)} ≤ sInf {s : ℝ | v ≤ μ.real (Iic s)} := by
  apply (source_quantile_le_iff μ hu).2
  exact huv.trans ((source_quantile_le_iff μ hv).1 le_rfl)

/-- Increasing approximations of an interior level have increasing quantiles. -/
theorem source_quantile_sequence_monotone (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) {v : ℕ → ℝ}
    (hv : ∀ n, 0 < v n ∧ v n ≤ u) (hm : Monotone v) :
    Monotone (fun n => sInf {s : ℝ | v n ≤ μ.real (Iic s)}) := by
  intro m n hmn
  exact source_quantile_mono μ ⟨(hv m).1, (hv m).2.trans_lt hu.2⟩
    ⟨(hv n).1, (hv n).2.trans_lt hu.2⟩ (hm hmn)

/-- Approximation from below never exceeds the terminal quantile. -/
theorem source_quantile_sequence_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) {v : ℕ → ℝ}
    (hv : ∀ n, 0 < v n ∧ v n ≤ u) (n : ℕ) :
    sInf {s : ℝ | v n ≤ μ.real (Iic s)} ≤ sInf {s : ℝ | u ≤ μ.real (Iic s)} :=
  source_quantile_mono μ ⟨(hv n).1, (hv n).2.trans_lt hu.2⟩ hu (hv n).2

/-- Quantiles converge under approximation of a level from below, including
at atoms. The convergence of levels is an input; quantile convergence is proved. -/
theorem tendsto_source_quantile_from_below (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) {v : ℕ → ℝ}
    (hv : ∀ n, 0 < v n ∧ v n ≤ u) (hl : Tendsto v atTop (𝓝 u)) :
    Tendsto (fun n => sInf {s : ℝ | v n ≤ μ.real (Iic s)}) atTop
      (𝓝 (sInf {s : ℝ | u ≤ μ.real (Iic s)})) := by
  apply tendsto_order.2
  constructor
  · intro t ht
    have hF : μ.real (Iic t) < u := by
      by_contra h
      exact (not_le_of_gt ht) ((source_quantile_le_iff μ hu).2 (le_of_not_gt h))
    filter_upwards [hl.eventually (eventually_gt_nhds hF)] with n hn
    exact lt_source_quantile μ hn ((hv n).2.trans_lt hu.2)
  · intro t ht
    exact Eventually.of_forall fun n => (source_quantile_sequence_le μ hu hv n).trans_lt ht

/-- Measurability uses the open-interval carrier, with no endpoint value. -/
theorem measurable_source_quantile (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Measurable (fun u : {u : ℝ // u ∈ Ioo (0 : ℝ) 1} =>
      sInf {s : ℝ | (u : ℝ) ≤ μ.real (Iic s)}) := by
  apply Monotone.measurable
  intro u v huv
  exact source_quantile_mono μ u.property v.property huv

end LPPDifferentiability
