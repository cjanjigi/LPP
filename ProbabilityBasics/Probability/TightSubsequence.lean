/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.TightProduct
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.Sequences

/-!
# A weak subsequence from tight coordinate laws

The limit is a probability measure. Convergence is in the weak sense: the
integrals of bounded continuous functions converge. This is the weak
subsequence step that follows (2.12) of Liggett (1985).
-/

public section

open MeasureTheory Set Filter
open scoped Topology

namespace LPPDifferentiability

/-- Tight coordinate laws of a sequence on the countable real product give a
strictly increasing subsequence converging weakly to a probability measure. -/
theorem exists_probabilityMeasure_tendsto_subseq_of_coordinate_tight
    (μ : ℕ → ProbabilityMeasure (ℕ → ℝ))
    (hμ : ∀ k : ℕ, IsTightMeasureSet
      (Set.range fun n : ℕ ↦ Measure.map (Function.eval k) (μ n : Measure (ℕ → ℝ)))) :
    ∃ ν : ProbabilityMeasure (ℕ → ℝ), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (μ ∘ φ) atTop (𝓝 ν) := by
  have htight : IsTightMeasureSet
      {((ν : ProbabilityMeasure (ℕ → ℝ)) : Measure (ℕ → ℝ)) | ν ∈ Set.range μ} := by
    apply isTightMeasureSet_of_coordinate_maps
    intro k
    convert hμ k using 1
    ext κ
    simp only [mem_image, mem_ofPred_eq, mem_range, exists_exists_eq_and]
  obtain ⟨ν, _, φ, hφ, hlim⟩ :=
    (isCompact_closure_of_isTightMeasureSet htight).tendsto_subseq
      (fun n ↦ subset_closure (mem_range_self n))
  exact ⟨ν, φ, hφ, hlim⟩

end LPPDifferentiability
