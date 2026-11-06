/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Tightness from coordinate laws

A family of measures on the countable product `ℕ → ℝ` is tight when each of
its coordinate marginals is tight. This is the tightness step behind the weak
subsequence assertion that follows (2.12) of Liggett (1985). The family may
consist of arbitrary measures; no independence or product-form assumption is used.
-/

public section

open MeasureTheory Set

namespace LPPDifferentiability

/-- A family of measures on the countable real product is tight whenever each
family of coordinate pushforwards is tight. -/
theorem isTightMeasureSet_of_coordinate_maps
    (S : Set (Measure (ℕ → ℝ)))
    (hS : ∀ n : ℕ, IsTightMeasureSet ((Measure.map (Function.eval n)) '' S)) :
    IsTightMeasureSet S := by
  classical
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨δ, hδpos, hδsum⟩ :=
    ENNReal.exists_pos_sum_of_countable' hε.ne' ℕ
  have hcoord : ∀ n : ℕ, ∃ K : Set ℝ, IsCompact K ∧
      ∀ μ ∈ S, (Measure.map (Function.eval n) μ) Kᶜ ≤ δ n := by
    intro n
    obtain ⟨K, hK, hbound⟩ :=
      isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp (hS n) (δ n) (hδpos n)
    exact ⟨K, hK, fun μ hμ ↦ hbound _ (mem_image_of_mem _ hμ)⟩
  choose K hK hbound using hcoord
  refine ⟨{x : ℕ → ℝ | ∀ n, x n ∈ K n}, isCompact_pi_infinite hK, ?_⟩
  intro μ hμ
  have hcompl : {x : ℕ → ℝ | ∀ n, x n ∈ K n}ᶜ =
      ⋃ n : ℕ, (Function.eval n) ⁻¹' (K n)ᶜ := by
    ext x
    simp only [mem_compl_iff, mem_ofPred_eq, not_forall, mem_iUnion, mem_preimage,
      Function.eval]
  rw [hcompl]
  calc
    μ (⋃ n : ℕ, (Function.eval n) ⁻¹' (K n)ᶜ)
        ≤ ∑' n : ℕ, μ ((Function.eval n) ⁻¹' (K n)ᶜ) := measure_iUnion_le _
    _ ≤ ∑' n : ℕ, δ n := ENNReal.tsum_le_tsum fun n ↦ by
      rw [← Measure.map_apply (measurable_pi_apply n) (hK n).isClosed.measurableSet.compl]
      exact hbound n μ hμ
    _ ≤ ε := hδsum.le

end LPPDifferentiability
