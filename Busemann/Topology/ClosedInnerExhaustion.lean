/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.Compactness.Compact

/-! A uniform closed inner exhaustion for an open set in a pseudometrizable space. -/

@[expose] public section
open Filter
namespace LPP.Busemann

/-- One open set has an increasing closed inner exhaustion whose interiors
cover it; the same sequence captures every compact subset of that open set. -/
theorem exists_closed_inner_exhaustion_of_isOpen
    {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.PseudoMetrizableSpace X]
    {U : Set X} (hU : IsOpen U) :
    ∃ F : ℕ → Set X,
      (∀ n, IsClosed (F n)) ∧
      (∀ n, F n ⊆ U) ∧
      Monotone F ∧
      U ⊆ ⋃ n, interior (F n) ∧
      ∀ K : Set X, IsCompact K → K ⊆ U → ∃ n, K ⊆ F n := by
  classical
  let : PseudoMetricSpace X :=
    TopologicalSpace.pseudoMetrizableSpacePseudoMetric X
  obtain ⟨a, ha_pos, ha_lt_one⟩ : ∃ a : ENNReal, 0 < a ∧ a < 1 :=
    exists_between zero_lt_one
  let F : ℕ → Set X := fun n => {x | a ^ n ≤ Metric.infEDist x Uᶜ}
  have hClosed (n : ℕ) : IsClosed (F n) := by
    change IsClosed ((fun x : X => Metric.infEDist x Uᶜ) ⁻¹' Set.Ici (a ^ n))
    exact IsClosed.preimage Metric.continuous_infEDist isClosed_Ici
  have hSubset (n : ℕ) : F n ⊆ U := by
    intro x hx
    by_contra hxU
    have hxComp : x ∈ Uᶜ := by simpa using hxU
    have hdist : Metric.infEDist x Uᶜ ≠ 0 :=
      ((ENNReal.pow_pos ha_pos n).trans_le hx).ne'
    exact hdist (Metric.infEDist_zero_of_mem hxComp)
  have hMono : Monotone F := by
    intro m n hmn x hx
    change a ^ m ≤ Metric.infEDist x Uᶜ at hx
    change a ^ n ≤ Metric.infEDist x Uᶜ
    exact (pow_le_pow_right_of_le_one' ha_lt_one.le hmn).trans hx
  have hpow := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one ha_lt_one
  let G : ℕ → Set X := fun n => {x | a ^ n < Metric.infEDist x Uᶜ}
  have hGOpen (n : ℕ) : IsOpen (G n) := by
    change IsOpen ((fun x : X => Metric.infEDist x Uᶜ) ⁻¹' Set.Ioi (a ^ n))
    exact IsOpen.preimage Metric.continuous_infEDist isOpen_Ioi
  have hGSubset (n : ℕ) : G n ⊆ F n := by
    intro x hx
    change a ^ n < Metric.infEDist x Uᶜ at hx
    exact le_of_lt hx
  have hInteriorCover : U ⊆ ⋃ n, interior (F n) := by
    intro x hx
    have hxNotComp : x ∉ Uᶜ := by simpa using hx
    have hdistPos : 0 < Metric.infEDist x Uᶜ := by
      rw [Metric.mem_iff_infEDist_zero_of_closed hU.isClosed_compl] at hxNotComp
      simpa [pos_iff_ne_zero] using hxNotComp
    obtain ⟨n, hn⟩ := ((tendsto_order.1 hpow).2 _ hdistPos).exists
    refine Set.mem_iUnion.mpr ⟨n, ?_⟩
    exact interior_maximal (hGSubset n) (hGOpen n) hn
  have hCompactCapture :
      ∀ K : Set X, IsCompact K → K ⊆ U → ∃ n, K ⊆ F n := by
    intro K hK hKU
    obtain ⟨n, hn⟩ :=
      hK.elim_directed_cover
        (fun n => interior (F n))
        (fun n => isOpen_interior)
        (hKU.trans hInteriorCover)
        (Monotone.directed_le fun i j hij => interior_mono (hMono hij))
    exact ⟨n, hn.trans interior_subset⟩
  exact ⟨F, hClosed, hSubset, hMono, hInteriorCover, hCompactCapture⟩

end LPP.Busemann
