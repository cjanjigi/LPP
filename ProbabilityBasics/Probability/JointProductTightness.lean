/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.TightMoment
public import Mathlib.Topology.MetricSpace.Polish
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-!
# Joint tightness with a fixed first marginal

These generic conditional helpers retain the joint laws. They do not
construct a coupling or assume independence. `PolishSpace X` means that the
topology is separable and admits a complete compatible metric; `BorelSpace X`
identifies the measurable sets with the Borel sets of that topology.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace LPPDifferentiability

/-- Tight integer-coordinate laws give tightness on the whole sequence space.
The cutoffs have summable tail errors; their product is compact. -/
theorem isTightMeasureSet_of_int_coordinate_maps
    (S : Set (Measure (ℤ → ℝ)))
    (hS : ∀ j : ℤ, IsTightMeasureSet ((Measure.map (Function.eval j)) '' S)) :
    IsTightMeasureSet S := by
  classical
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨δ, hδpos, hδsum⟩ := ENNReal.exists_pos_sum_of_countable' hε.ne' ℤ
  have hcoord : ∀ j : ℤ, ∃ K : Set ℝ, IsCompact K ∧
      ∀ μ ∈ S, (Measure.map (Function.eval j) μ) Kᶜ ≤ δ j := by
    intro j
    obtain ⟨K, hK, hbound⟩ :=
      isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp (hS j) (δ j) (hδpos j)
    exact ⟨K, hK, fun μ hμ ↦ hbound _ (mem_image_of_mem _ hμ)⟩
  choose K hK hbound using hcoord
  refine ⟨{z : ℤ → ℝ | ∀ j, z j ∈ K j}, isCompact_pi_infinite hK, ?_⟩
  intro μ hμ
  have hcompl : {z : ℤ → ℝ | ∀ j, z j ∈ K j}ᶜ =
      ⋃ j : ℤ, (Function.eval j) ⁻¹' (K j)ᶜ := by
    ext z
    simp only [mem_compl_iff, mem_ofPred_eq, not_forall, mem_iUnion, mem_preimage,
      Function.eval]
  rw [hcompl]
  calc
    μ (⋃ j : ℤ, (Function.eval j) ⁻¹' (K j)ᶜ)
        ≤ ∑' j : ℤ, μ ((Function.eval j) ⁻¹' (K j)ᶜ) := measure_iUnion_le _
    _ ≤ ∑' j : ℤ, δ j := ENNReal.tsum_le_tsum fun j ↦ by
      rw [← Measure.map_apply (measurable_pi_apply j) (hK j).isClosed.measurableSet.compl]
      exact hbound j μ hμ
    _ ≤ ε := hδsum.le

variable {X : Type*} [TopologicalSpace X] [PolishSpace X]
  [MeasurableSpace X] [BorelSpace X]

/-- Finite first absolute moments, uniform in the sequence index separately
for every integer coordinate, and an exactly fixed first marginal imply
joint tightness. No moment bound on the first marginal is required. -/
theorem isTightMeasureSet_joint_of_coordinate_moments
    (ρ : ProbabilityMeasure X) (ν : ℕ → ProbabilityMeasure (X × (ℤ → ℝ)))
    (hfst : ∀ n, (ν n : Measure (X × (ℤ → ℝ))).fst = (ρ : Measure X))
    (C : ℤ → ℝ≥0∞) (hC : ∀ j, C j ≠ ∞)
    (hbound : ∀ n j, (∫⁻ p : X × (ℤ → ℝ), ENNReal.ofReal ‖p.2 j‖
      ∂(ν n : Measure (X × (ℤ → ℝ)))) ≤ C j) :
    IsTightMeasureSet (Set.range fun n => (ν n : Measure (X × (ℤ → ℝ)))) := by
  apply IsTightMeasureSet.prodMk
  · apply (isTightMeasureSet_singleton (μ := (ρ : Measure X))).subset
    rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
    exact Set.mem_singleton_iff.mpr (hfst n)
  · apply isTightMeasureSet_of_int_coordinate_maps
    intro j
    apply isTightMeasureSet_of_lintegral_abs_le _ (C j) (hC j)
    rintro _ ⟨_, ⟨_, ⟨n, rfl⟩, rfl⟩, rfl⟩
    rw [Measure.snd, lintegral_map (f := fun x : ℝ => ENNReal.ofReal ‖x‖)
      (ENNReal.measurable_ofReal.comp measurable_norm) (measurable_pi_apply j),
      lintegral_map (f := fun z : ℤ → ℝ => ENNReal.ofReal ‖z j‖)
        ((ENNReal.measurable_ofReal.comp measurable_norm).comp (measurable_pi_apply j))
        measurable_snd]
    exact hbound n j

/-- One weak joint subsequential limit retains the given first marginal.
The subsequence is strictly increasing, and all coordinates share its limit. -/
theorem exists_joint_probabilityMeasure_tendsto_subseq_of_coordinate_moments
    (ρ : ProbabilityMeasure X) (ν : ℕ → ProbabilityMeasure (X × (ℤ → ℝ)))
    (hfst : ∀ n, (ν n : Measure (X × (ℤ → ℝ))).fst = (ρ : Measure X))
    (C : ℤ → ℝ≥0∞) (hC : ∀ j, C j ≠ ∞)
    (hbound : ∀ n j, (∫⁻ p : X × (ℤ → ℝ), ENNReal.ofReal ‖p.2 j‖
      ∂(ν n : Measure (X × (ℤ → ℝ)))) ≤ C j) :
    ∃ κ : ProbabilityMeasure (X × (ℤ → ℝ)), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (ν ∘ φ) atTop (𝓝 κ) ∧
      (κ : Measure (X × (ℤ → ℝ))).fst = (ρ : Measure X) := by
  have htight : IsTightMeasureSet
      {((κ : ProbabilityMeasure (X × (ℤ → ℝ))) : Measure (X × (ℤ → ℝ))) |
        κ ∈ Set.range ν} := by
    convert isTightMeasureSet_joint_of_coordinate_moments ρ ν hfst C hC hbound using 1
    ext μ
    simp only [mem_ofPred_eq, mem_range, exists_exists_eq_and]
  obtain ⟨κ, _, φ, hφ, hlim⟩ :=
    (isCompact_closure_of_isTightMeasureSet htight).tendsto_subseq
      (fun n ↦ subset_closure (mem_range_self n))
  refine ⟨κ, φ, hφ, hlim, ?_⟩
  have hmap := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (ν ∘ φ) κ hlim continuous_fst
  have heq : (fun i => ((ν ∘ φ) i).map Prod.fst) = fun _ : ℕ => ρ := by
    funext i
    apply Subtype.ext
    exact hfst (φ i)
  rw [heq] at hmap
  have hκ : κ.map Prod.fst = ρ := tendsto_nhds_unique hmap tendsto_const_nhds
  exact congrArg (fun m : ProbabilityMeasure X => (m : Measure X)) hκ

end LPPDifferentiability
