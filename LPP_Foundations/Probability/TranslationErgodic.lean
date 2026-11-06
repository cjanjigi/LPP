/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Probability.TranslationCylinder
public import LPP_Foundations.Probability.FiniteCoordinateApprox
public import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.MeasureTheory.Measure.Real

/-!
# Ergodicity of nonzero canonical iid translations

Approximate a strictly invariant event by a finite-coordinate event. A sufficiently
large iterate separates the finite supports, so iid independence gives product
probability. Symmetric-difference errors then give the invariant event probability
as its own square, hence zero or one.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal symmDiff

namespace LPPDifferentiability

/-- A strictly invariant measurable event has probability zero or one under a
nonzero translation of the canonical iid environment. -/
theorem environmentLaw_invariant_zero_one (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (v : Lattice) (hv : v ≠ 0) {A : Set Environment} (hA : MeasurableSet A)
    (hinv : (fun ω : Environment => fun z => ω (v + z)) ⁻¹' A = A) :
    environmentLaw μ A = 0 ∨ environmentLaw μ A = 1 := by
  let ρ := environmentLaw μ
  let f : Environment → Environment := fun ω z => ω (v + z)
  have hf : MeasurePreserving f ρ ρ := measurePreserving_environment_translation μ v
  have ha0 : 0 ≤ ρ.real A := measureReal_nonneg
  have ha1 : ρ.real A ≤ 1 := measureReal_le_one
  have hsquare : ρ.real A = ρ.real A * ρ.real A := by
    have hlow : ρ.real A * ρ.real A ≤ ρ.real A := by nlinarith only [ha0, ha1]
    apply le_antisymm ?_ hlow
    by_contra! hgap
    let δ : ℝ := (ρ.real A - ρ.real A * ρ.real A) / 8
    have hδ : 0 < δ := by dsimp [δ]; linarith only [hgap]
    obtain ⟨S, B, hB, herr⟩ := exists_finite_coordinate_approx μ hA hδ
    let C : Set Environment := {ω | (fun z : {z : Lattice // z ∈ S} => ω z.val) ∈ B}
    have hC : MeasurableSet C := measurableSet_environment_restrict S hB
    have he : ρ.real (A ∆ C) < δ := by
      have h := ENNReal.toReal_strict_mono ENNReal.ofReal_ne_top herr
      simpa only [measureReal_def, ρ, C, ENNReal.toReal_ofReal (le_of_lt hδ)] using h
    obtain ⟨n, hn⟩ := (eventually_environmentLaw_cylinder_inter_iterate μ v hv S B hB).exists
    have hfn := hf.iterate n
    have hAn : f^[n] ⁻¹' A = A := Function.IsFixedPt.preimage_iterate hinv n
    have hCn : MeasurableSet (f^[n] ⁻¹' C) := hC.preimage hfn.measurable
    have hprod : ρ.real (C ∩ f^[n] ⁻¹' C) = ρ.real C * ρ.real C := by
      change (environmentLaw μ (C ∩ f^[n] ⁻¹' C)).toReal =
        (environmentLaw μ C).toReal * (environmentLaw μ C).toReal
      rw [hn, ENNReal.toReal_mul]
    have hsubset : A ∆ (C ∩ f^[n] ⁻¹' C) ⊆
        (A ∆ C) ∪ f^[n] ⁻¹' (A ∆ C) := by
      rw [preimage_symmDiff, hAn]
      intro x hx
      simp only [mem_symmDiff, mem_inter_iff, mem_union] at hx ⊢
      tauto
    have herror : ρ.real (A ∆ (C ∩ f^[n] ⁻¹' C)) ≤ 2 * ρ.real (A ∆ C) := by
      calc
        _ ≤ ρ.real ((A ∆ C) ∪ f^[n] ⁻¹' (A ∆ C)) := measureReal_mono hsubset
        _ ≤ ρ.real (A ∆ C) + ρ.real (f^[n] ⁻¹' (A ∆ C)) := measureReal_union_le _ _
        _ = 2 * ρ.real (A ∆ C) := by
          rw [hfn.measureReal_preimage (hA.symmDiff hC).nullMeasurableSet]
          ring
    have hcompare := abs_measureReal_sub_le_measureReal_symmDiff
      hA.nullMeasurableSet (hC.inter hCn).nullMeasurableSet (μ := ρ)
    have habs := abs_measureReal_sub_le_measureReal_symmDiff
      hA.nullMeasurableSet hC.nullMeasurableSet (μ := ρ)
    have hac : |ρ.real A - ρ.real C| < δ := lt_of_le_of_lt habs he
    have hc0 : 0 ≤ ρ.real C := measureReal_nonneg
    have hc1 : ρ.real C ≤ 1 := measureReal_le_one
    have hc_square : ρ.real C * ρ.real C ≤ ρ.real A * ρ.real A + 2 * δ := by
      by_cases hca : ρ.real C ≤ ρ.real A
      · have h := mul_self_le_mul_self hc0 hca
        nlinarith only [h, hδ]
      · have hd : ρ.real C - ρ.real A ≤ δ := by
          have := (abs_lt.mp hac).1
          linarith only [this]
        have hsum : ρ.real C + ρ.real A ≤ 2 := by linarith only [hc1, ha1]
        have hmul := mul_le_mul hd hsum (by positivity : 0 ≤ ρ.real C + ρ.real A)
          (le_of_lt hδ)
        nlinarith only [hmul]
    have hcmp : ρ.real A ≤ ρ.real C * ρ.real C + 2 * ρ.real (A ∆ C) := by
      have hh := (abs_le.mp hcompare).2
      rw [hprod] at hh
      linarith only [hh, herror]
    dsimp [δ] at hc_square he
    linarith only [hcmp, hc_square, he, hgap]
  have hcases : ρ.real A = 0 ∨ ρ.real A = 1 := by
    have hmul : ρ.real A * (ρ.real A - 1) = 0 := by nlinarith only [hsquare]
    rcases mul_eq_zero.mp hmul with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  rcases hcases with h | h
  · exact Or.inl ((measureReal_eq_zero_iff).mp h)
  · exact Or.inr ((ENNReal.toReal_eq_one_iff _).mp h)

/-- Every nonzero integer translation of the canonical iid environment is ergodic,
including for atomic or degenerate one-site probability laws. -/
theorem ergodic_environment_translation (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (v : Lattice) (hv : v ≠ 0) :
    Ergodic (fun ω : Environment => fun z => ω (v + z)) (environmentLaw μ) := by
  refine ⟨measurePreserving_environment_translation μ v, ⟨?_⟩⟩
  intro A hA hinv
  rw [eventuallyEmptyOrUniv_iff]
  rcases environmentLaw_invariant_zero_one μ v hv hA hinv with h | h
  · exact Or.inr (compl_mem_ae_iff.mpr h)
  · exact Or.inl ((mem_ae_iff_prob_eq_one hA).mpr h)

end LPPDifferentiability
