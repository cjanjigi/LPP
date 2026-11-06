/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.BirkhoffPointwise
public import Mathlib.Dynamics.Ergodic.Function

/-! # Ergodic Birkhoff averages -/

public section

open MeasureTheory Filter
open scoped Topology

namespace LPPDifferentiability

/-- An integrable almost-everywhere invariant real function under an ergodic
probability-preserving map equals its integral almost everywhere. -/
theorem ae_eq_integral_of_ergodic_invariant {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω} {g : Ω → ℝ}
    (hT : Ergodic T μ) (hg : Integrable g μ)
    (hginv : ∀ᵐ ω ∂μ, g (T ω) = g ω) :
    g =ᵐ[μ] fun _ => ∫ ω, g ω ∂μ := by
  obtain ⟨c, hgc⟩ := hT.ae_eq_const_of_ae_eq_comp_ae hg.aestronglyMeasurable hginv
  have hmean : (∫ ω, g ω ∂μ) = c := by
    calc
      (∫ ω, g ω ∂μ) = ∫ _ : Ω, c ∂μ := integral_congr_ae hgc
      _ = c := by simp
  filter_upwards [hgc] with ω hω
  exact hω.trans hmean.symm

/-- For an ergodic probability-preserving map, the actual forward averages of
an integrable measurable real observable converge almost everywhere to its
integral. -/
theorem ae_tendsto_birkhoffAverage_integral_of_ergodic {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → Ω} {f : Ω → ℝ} (hT : Ergodic T μ)
    (hm : Measurable f) (hi : Integrable f μ) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => birkhoffAverage ℝ T f n ω) atTop
        (𝓝 (∫ ω, f ω ∂μ)) := by
  obtain ⟨g, hgm, hgi, hlim, hginv, hmean⟩ :=
    exists_birkhoffPointwise hT.toMeasurePreserving hm hi
  have hgeq := ae_eq_integral_of_ergodic_invariant hT hgi hginv
  filter_upwards [hlim, hgeq] with ω hω heq
  simpa only [heq, hmean] using hω

end LPPDifferentiability
