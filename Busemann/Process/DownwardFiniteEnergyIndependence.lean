/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Frozen.Definitions.DownwardFiniteEnergy
public import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.ConditionalExpectation

/-! A conditional-expectation criterion for downward finite energy. -/

@[expose] public section

open MeasureTheory ProbabilityTheory LPPDifferentiability

namespace LPP.Busemann

/-- If the weight at a site is measurable and independent of the complete
outside array, then positive site events have positive conditional probability
given the outside field. This is the single-site conditional-expectation step
parameterized from the origin argument in GRS, arXiv:1510.00860v1, Appendix A,
lines 1440–1470. -/
theorem ae_singleton_outside_condExp_pos_of_indep
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : @MeasureTheory.Measure Ω mΩ) [IsProbabilityMeasure P]
    (weights : Ω → Environment)
    (B : Lattice → Lattice → Ω → ℝ)
    (z : Lattice)
    (hSite : Measurable (fun ω : Ω => weights ω z))
    (hOutside : Measurable (outsideWeightsAndCocycleIncrements weights B {z}))
    (hIndep : IndepFun (fun ω : Ω => weights ω z)
      (outsideWeightsAndCocycleIncrements weights B {z}) P) :
    ∀ (K : ℝ), 0 < P {ω : Ω | weights ω z ≤ K} →
      ∀ᵐ ω ∂P, 0 < (MeasureTheory.condExp
        (outsideSigma weights B {z}) P
        (Set.indicator {ω : Ω | weights ω z ≤ K}
          (fun _ => (1 : ℝ)))) ω := by
  classical
  intro K hMass

  let mSite : MeasurableSpace Ω :=
    MeasurableSpace.comap (fun ω : Ω => weights ω z)
      (inferInstance : MeasurableSpace ℝ)
  let mOutside : MeasurableSpace Ω := outsideSigma weights B {z}
  let fK : Ω → ℝ :=
    Set.indicator {ω : Ω | weights ω z ≤ K} (fun _ => (1 : ℝ))

  -- The two generated fields stay inside the original ambient field.
  have hSiteLe : mSite ≤ mΩ := hSite.comap_le
  have hOutsideLe : mOutside ≤ mΩ := hOutside.comap_le

  -- Function independence is independence of the generated fields.
  have hFieldIndep : Indep mSite mOutside P := by
    exact (IndepFun_iff_Indep (fun ω : Ω => weights ω z)
      (outsideWeightsAndCocycleIncrements weights B {z}) P).mp hIndep

  -- A probability measure has a sigma-finite trim to the outside field.
  have : SigmaFinite (P.trim hOutsideLe) := by infer_instance

  -- The site event is measurable in both its generated field and the ambient one.
  have hEventSite :
      MeasurableSet[mSite] {ω : Ω | weights ω z ≤ K} := by
    have hSiteGenerated :
        Measurable[mSite] (fun ω : Ω => weights ω z) :=
      comap_measurable (fun ω : Ω => weights ω z)
    exact measurableSet_le hSiteGenerated measurable_const
  have hEventAmbient :
      MeasurableSet[mΩ] {ω : Ω | weights ω z ≤ K} :=
    measurableSet_le hSite measurable_const
  have hfK : StronglyMeasurable[mSite] fK := by
    dsimp [fK]
    exact StronglyMeasurable.indicator stronglyMeasurable_const hEventSite

  -- Independence makes the conditional expectation equal to the event's mass.
  have hConditional :
      P[fK | mOutside] =ᵐ[P] fun _ : Ω => ∫ ω, fK ω ∂P :=
    condExp_indep_eq hSiteLe hOutsideLe hfK hFieldIndep
  have hIntegral :
      (∫ ω, fK ω ∂P) = P.real {ω : Ω | weights ω z ≤ K} :=
    integral_indicator_one hEventAmbient
  have hRealMass : 0 < P.real {ω : Ω | weights ω z ≤ K} := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos hMass.ne' (measure_ne_top P _)

  filter_upwards [hConditional] with ω hω
  change 0 < P[fK | mOutside] ω
  rw [hω, hIntegral]
  exact hRealMass

/-- If the origin weight is measurable and independent of the complete outside
array, then positive origin events have positive conditional probability given
the outside field. This is the conditional-expectation step in GRS,
arXiv:1510.00860v1, Appendix A, lines 1440–1470. -/
theorem hasDownwardFiniteEnergy_of_origin_outsideArray_indep
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : @MeasureTheory.Measure Ω mΩ) [IsProbabilityMeasure P]
    (weights : Ω → Environment)
    (B : Lattice → Lattice → Ω → ℝ)
    (hOrigin : Measurable (fun ω : Ω => weights ω 0))
    (hOutside : Measurable (outsideWeightsAndCocycleIncrements weights B {0}))
    (hIndep : IndepFun (fun ω : Ω => weights ω 0)
      (outsideWeightsAndCocycleIncrements weights B {0}) P) :
    HasDownwardFiniteEnergy P weights B := by
  classical
  unfold HasDownwardFiniteEnergy
  exact ae_singleton_outside_condExp_pos_of_indep
    P weights B 0 hOrigin hOutside hIndep

end LPP.Busemann
