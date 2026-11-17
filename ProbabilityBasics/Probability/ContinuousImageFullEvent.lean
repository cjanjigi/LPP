/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

@[expose] public section

open MeasureTheory TopologicalSpace
open scoped ENNReal

namespace ProbabilityBasics

/-- A continuous image of a measurable full event contains a measurable full event
for the image measure. -/
theorem exists_measurable_full_subset_image_of_continuous
    {α β : Type*} [TopologicalSpace α] [SecondCountableTopology α]
    [IsCompletelyPseudoMetrizableSpace α] [MeasurableSpace α] [BorelSpace α]
    [TopologicalSpace β] [T2Space β] [MeasurableSpace β] [BorelSpace β]
    (P : Measure α) [IsProbabilityMeasure P]
    (f : α → β) (hf : Continuous f)
    (E : Set α) (hE : MeasurableSet E) (hEfull : P E = 1) :
    ∃ F : Set β, MeasurableSet F ∧ F ⊆ f '' E ∧ (P.map f) F = 1 := by
  classical
  have happrox : ∀ n : ℕ, ∃ K : Set α, K ⊆ E ∧
      (IsCompact K ∧ IsClosed K) ∧ P E < P K + (n : ℝ≥0∞)⁻¹ := by
    intro n
    apply (innerRegular_isCompact_isClosed_measurableSet_of_finite P).exists_subset_lt_add
      ⟨isCompact_empty, isClosed_empty⟩ hE
    · rw [hEfull]
      exact ENNReal.one_ne_top
    · simp
  choose K hKE hK hmass using happrox
  let F : Set β := ⋃ n, f '' K n
  have hF : MeasurableSet F := by
    exact MeasurableSet.iUnion fun n => ((hK n).1.image hf).isClosed.measurableSet
  have hFE : F ⊆ f '' E := by
    intro y hy
    obtain ⟨n, x, hx, rfl⟩ := Set.mem_iUnion.mp hy
    exact ⟨x, hKE n hx, rfl⟩
  have hbound (n : ℕ) : P E ≤ P (f ⁻¹' F) + (n : ℝ≥0∞)⁻¹ := by
    have hKbound : P (K n) ≤ P (f ⁻¹' F) := by
      apply measure_mono
      intro x hx
      exact Set.mem_iUnion.mpr ⟨n, x, hx, rfl⟩
    exact (hmass n).le.trans (add_le_add hKbound le_rfl)
  have ht : Filter.Tendsto (fun n : ℕ => P (f ⁻¹' F) + (n : ℝ≥0∞)⁻¹)
      Filter.atTop (nhds (P (f ⁻¹' F))) := by
    simpa only [add_zero] using
      (tendsto_const_nhds.add ENNReal.tendsto_inv_nat_nhds_zero)
  have hlower : 1 ≤ P (f ⁻¹' F) := by
    rw [← hEfull]
    exact ge_of_tendsto' ht hbound
  have hupper : P (f ⁻¹' F) ≤ 1 := by
    simpa only [measure_univ] using
      (measure_mono (Set.subset_univ (f ⁻¹' F)) : P (f ⁻¹' F) ≤ P Set.univ)
  refine ⟨F, hF, hFE, ?_⟩
  rw [Measure.map_apply hf.measurable hF]
  exact le_antisymm hupper hlower

end ProbabilityBasics
