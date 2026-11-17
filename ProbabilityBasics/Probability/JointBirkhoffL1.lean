/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProbabilityBasics.Probability.BirkhoffCommutingInvariant
public import ProbabilityBasics.Probability.BirkhoffL1Contraction
import Mathlib.Tactic

/-! Two commuting Birkhoff limits and their joint L¹ error. -/

public section

open MeasureTheory Filter
open scoped Topology

namespace ProbabilityBasics

/-- Two commuting preserving maps have one joint invariant L¹ limit for
nested averages, with both strict invariant-set mean identities. This is
an intermediate norm step in Krengel's finite-measure identification. -/
theorem exists_joint_birkhoffL1_limit
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S T : Ω → Ω) (hS : MeasurePreserving S μ μ) (hT : MeasurePreserving T μ μ)
    (hcomm : Function.Commute S T) (f : Ω → ℝ) (hf : Integrable f μ) :
    ∃ g : Ω → ℝ, Measurable g ∧ Integrable g μ ∧
      (∀ᵐ s ∂μ, g (S s) = g s) ∧ (∀ᵐ s ∂μ, g (T s) = g s) ∧
      (∀ A : Set Ω, MeasurableSet A → S ⁻¹' A = A → T ⁻¹' A = A →
        (∫ s in A, g s ∂μ) = ∫ s in A, f s ∂μ) ∧
      (∀ a c : ℕ → ℕ, Tendsto a atTop atTop → Tendsto c atTop atTop →
        Tendsto (fun n : ℕ => ∫ s,
          |birkhoffAverage ℝ S (birkhoffAverage ℝ T f (c n)) (a n) s - g s| ∂μ)
          atTop (𝓝 0)) := by
  obtain ⟨v, hvm, hvi, hvT, hvL1, hvMean⟩ :=
    exists_birkhoffL1_invariant_set_integrals μ T hT f hf
  obtain ⟨g, hgm, hgi, hgS, hgT, hgL1, hgMean⟩ :=
    exists_birkhoffL1_invariant_of_commute μ T S hT hS hcomm.symm v hvi hvT
  refine ⟨g, hgm, hgi, hgS, hgT, ?_, ?_⟩
  · intro A hA hAS hAT
    exact (hgMean A hA hAS).trans (hvMean A hA hAT)
  · intro a c ha hc
    let E : ℕ → ℝ := fun n => ∫ s,
      |birkhoffAverage ℝ S (birkhoffAverage ℝ T f (c n)) (a n) s - g s| ∂μ
    let E1 : ℕ → ℝ := fun n => ∫ s, |birkhoffAverage ℝ T f (c n) s - v s| ∂μ
    let E2 : ℕ → ℝ := fun n => ∫ s, |birkhoffAverage ℝ S v (a n) s - g s| ∂μ
    have hE1 : Tendsto E1 atTop (𝓝 0) := hvL1.comp hc
    have hE2 : Tendsto E2 atTop (𝓝 0) := hgL1.comp ha
    have hbound (n : ℕ) : E n ≤ E1 n + E2 n := by
      have hInner : Integrable (birkhoffAverage ℝ T f (c n)) μ :=
        LPPDifferentiability.integrable_birkhoffAverage hT hf (c n)
      have hOuter : Integrable (birkhoffAverage ℝ S (birkhoffAverage ℝ T f (c n)) (a n)) μ :=
        LPPDifferentiability.integrable_birkhoffAverage hS hInner (a n)
      have hOuterV : Integrable (birkhoffAverage ℝ S v (a n)) μ :=
        LPPDifferentiability.integrable_birkhoffAverage hS hvi (a n)
      have h1 : Integrable (fun s =>
          |birkhoffAverage ℝ S (birkhoffAverage ℝ T f (c n)) (a n) s -
            birkhoffAverage ℝ S v (a n) s|) μ := by
        simpa only [Pi.sub_apply] using (hOuter.sub hOuterV).abs
      have h2 : Integrable (fun s => |birkhoffAverage ℝ S v (a n) s - g s|) μ := by
        simpa only [Pi.sub_apply] using (hOuterV.sub hgi).abs
      have hsum := integral_mono ((hOuter.sub hgi).abs) (h1.add h2) (fun s =>
        abs_sub_le _ _ _)
      simp only [Pi.sub_apply, Pi.add_apply] at hsum
      rw [integral_add h1 h2] at hsum
      have hcontr := integral_abs_birkhoffAverage_sub_le μ S hS
        (birkhoffAverage ℝ T f (c n)) v hInner hvi (a n)
      dsimp [E, E1, E2]
      linarith only [hsum, hcontr]
    have htotal : Tendsto (fun n => E1 n + E2 n) atTop (𝓝 0) := by
      simpa only [add_zero] using hE1.add hE2
    exact squeeze_zero (fun n => integral_nonneg fun s => abs_nonneg _) hbound htotal

end ProbabilityBasics
