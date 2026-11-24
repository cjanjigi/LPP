/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.FlatTop.Percolation
public import Differentiability.Probability.TopIndicatorLaw

/-! The origin speed on a positive survival event is unique and transfers
from the Bernoulli indicator field to the real-weight law. -/

public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace LPPDifferentiability.FinalDraft

/-- Two limits of the actual right edge on a positive survival event coincide. -/
theorem isOriginRightEdgeSpeed_unique (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (M : ℝ) (hsurv : 0 < environmentLaw μ (orientedSiteSurvival M)) {β γ : ℝ}
    (hβ : IsOriginRightEdgeSpeed μ M β) (hγ : IsOriginRightEdgeSpeed μ M γ) : β = γ := by
  unfold IsOriginRightEdgeSpeed at hβ hγ
  obtain ⟨ω, hω, hωβ, hωγ⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hsurv.ne'
    (ae_mono Measure.restrict_le_self (hβ.and hγ))
  exact tendsto_nhds_unique (hωβ hω) (hωγ hω)

/-- The speed of the Bernoulli origin cluster is the speed of the actual
origin cluster in the weights at their finite support top. -/
theorem isOriginRightEdgeSpeed_of_bernoulli (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (M : ℝ) (hM : (M : EReal) = supportTop μ) {β : ℝ}
    (hβ : IsOriginRightEdgeSpeed
      (bernoulliMeasure (1 : ℝ) 0 ⟨μ.real {M}, by simp⟩) 1 β) :
    IsOriginRightEdgeSpeed μ M β := by
  let ν := bernoulliMeasure (1 : ℝ) 0 ⟨μ.real {M}, by simp⟩
  have hAtom : supportTopAtom μ = {M} := by
    ext t
    change (t : EReal) = supportTop μ ↔ t ∈ ({M} : Set ℝ)
    rw [← hM, EReal.coe_eq_coe_iff, mem_singleton_iff]
  have hlaw : (environmentLaw μ).map (topWeightIndicatorField μ) = environmentLaw ν := by
    rw [source_top_indicator_environmentLaw_map]
    simp only [environmentLaw, (source_top_indicator_hasLaw μ).map_eq, hAtom, ν]
  have hsites (ω : Environment) :
      {z | topWeightIndicatorField μ ω z = 1} = {z | ω z = M} := by
    ext z
    simp [topWeightIndicatorField, topWeightIndicator, ← hM, EReal.coe_eq_coe_iff]
  have hsurv (ω : Environment) (hω : ω ∈ orientedSiteSurvival M) :
      topWeightIndicatorField μ ω ∈ orientedSiteSurvival 1 := by
    obtain ⟨γ, hzero, hstep, htop⟩ := hω
    refine ⟨γ, hzero, hstep, fun n => ?_⟩
    have h : γ (n + 1) ∈ {z : Lattice | ω z = M} := htop n
    rwa [← hsites ω] at h
  unfold IsOriginRightEdgeSpeed at hβ ⊢
  rw [← hlaw] at hβ
  filter_upwards [ae_of_ae_map (measurable_source_top_indicator_environment μ).aemeasurable hβ]
    with ω hω h
  simpa only [hsites ω] using hω (hsurv ω h)

end LPPDifferentiability.FinalDraft
