/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.ConditionalPositive
public import ProbabilityBasics.Probability.ConditionalFiber

/-!
# Positive conditional modifications

A positive old event and an almost surely conditionally positive modification event give a
positive measurable event whose samples have actual old witnesses with the same observable.
-/

public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityBasics

/-- A conditionally positive modification event contains a positive measurable event whose samples
have old witnesses in `A` with the same value of `phi`, almost surely. This is the fixed-observable
probability step of GRS arXiv:1510.00860v1, Appendix A, Lemma A.2, reading lines 1441–1474. -/
theorem exists_positive_same_fiber_event
    {Ω E : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    [MeasurableSpace E] [MeasurableEq E]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    {phi : Ω → E} (hphi : Measurable phi)
    (A R : Set Ω) (hA : MeasurableSet A) (hR : MeasurableSet R)
    (hAPos : 0 < P A)
    (hRPos : ∀ᵐ s ∂P,
      0 < (MeasureTheory.condExp
        (MeasurableSpace.comap phi (inferInstance : MeasurableSpace E)) P
        (R.indicator fun _ : Ω => (1 : ℝ))) s) :
    ∃ D : Set Ω, MeasurableSet D ∧ 0 < P D ∧
      ∀ᵐ s2 ∂P, s2 ∈ D →
        s2 ∈ R ∧ ∃ s ∈ A, phi s = phi s2 := by
  let κ := ProbabilityTheory.condDistrib id phi P
  let D0 : Set Ω := {s | 0 < κ (phi s) A}

  -- The conditional mass and its positive set are measurable in the observable field.
  -- Inline the comap so the original ambient measurable-space instance stays in force.
  have hmass_observable :
      Measurable[MeasurableSpace.comap phi (inferInstance : MeasurableSpace E)]
        (fun s => κ (phi s) A) :=
    ProbabilityTheory.measurable_condDistrib hA
  have hD0_observable :
      MeasurableSet[MeasurableSpace.comap phi (inferInstance : MeasurableSpace E)] D0 :=
    measurableSet_lt measurable_const hmass_observable
  have hD0_measurable : MeasurableSet D0 := hphi.comap_le D0 hD0_observable
  have hmass_measurable : Measurable (fun s => κ (phi s) A) :=
    (ProbabilityTheory.Kernel.measurable_coe κ hA).comp hphi

  -- Disintegration preserves the total old-event mass, so its positive support has positive mass.
  have hmass_integral : (∫⁻ s, κ (phi s) A ∂P) = P A := by
    simpa only [Set.preimage_id, Set.univ_inter, Measure.restrict_univ] using
      (ProbabilityTheory.setLIntegral_condDistrib_of_measurableSet
        (μ := P) hphi aemeasurable_id hA (t := Set.univ) MeasurableSet.univ)
  have hmass_integral_pos : 0 < ∫⁻ s, κ (phi s) A ∂P := by
    rw [hmass_integral]
    exact hAPos
  have hD0_support : Function.support (fun s => κ (phi s) A) = D0 := by
    ext s
    simp only [Function.mem_support, D0, Set.mem_ofPred_eq, pos_iff_ne_zero]
  have hD0_pos : 0 < P D0 := by
    rw [← hD0_support]
    exact (lintegral_pos_iff_support hmass_measurable).1 hmass_integral_pos

  -- The conditional-positivity criterion gives a positive modification intersection.
  have hD_pos : 0 < P (R ∩ D0) :=
    (ae_condExp_indicator_pos_iff P
      (MeasurableSpace.comap phi (inferInstance : MeasurableSpace E))
      hphi.comap_le R hR).1 hRPos D0 hD0_observable hD0_pos
  refine ⟨R ∩ D0, hR.inter hD0_measurable, hD_pos, ?_⟩

  -- The fiber theorem turns positive conditional mass into an actual old witness.
  filter_upwards [ae_exists_mem_eq_of_condDistrib_pos P hphi A] with s2 hfiber
  intro hs2
  obtain ⟨s, hsA, hsame⟩ := hfiber hs2.2
  exact ⟨hs2.1, s, hsA, hsame⟩

end ProbabilityBasics
