/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.DownwardFiniteEnergyIndependence
public import Busemann.Frozen.Definitions.ForwardMeasurable
public import LPP_Foundations.Probability.CoordinateLaw
public import ProbabilityBasics.Probability.DisjointFamilies
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-! The canonical i.i.d. environment has downward finite energy under forward measurability. -/

@[expose] public section

open MeasureTheory ProbabilityTheory LPPDifferentiability

namespace LPP.Busemann

/-- Under forward measurability, every site with a positive lower-threshold
probability has positive conditional probability given the complete outside array.
This is the site version of GRS arXiv:1510.00860v1, Appendix A,
lines 1440–1470. -/
theorem ae_singleton_outside_condExp_pos_environmentLaw_of_isForwardMeasurable
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (B : Lattice → Lattice → Environment → ℝ)
    (hForward : IsForwardMeasurable B) :
    ∀ (z : Lattice) (K : ℝ),
      0 < (environmentLaw μ) {ω : Environment | ω z ≤ K} →
      ∀ᵐ ω ∂environmentLaw μ, 0 < (MeasureTheory.condExp
        (outsideSigma (fun ω : Environment => ω) B {z}) (environmentLaw μ)
        (Set.indicator {ω : Environment | ω z ≤ K}
          (fun _ => (1 : ℝ)))) ω := by
  classical
  intro site K hMass
  let mEnvironment : MeasurableSpace Environment := inferInstance
  let siteIndex : Set Lattice := {site}
  let awayIndex : Set Lattice := {z | z ≠ site}
  let siteEval : (siteIndex → ℝ) → ℝ :=
    fun a => a ⟨site, by simp [siteIndex]⟩
  let X : Environment → ℝ :=
    fun ω => siteEval (fun z : siteIndex => ω z.1)
  let H : Environment → (awayIndex → ℝ) := fun ω z => ω z.1
  let mSite : MeasurableSpace Environment :=
    MeasurableSpace.comap X (inferInstance : MeasurableSpace ℝ)
  let mAway : MeasurableSpace Environment :=
    MeasurableSpace.comap H (inferInstance : MeasurableSpace (awayIndex → ℝ))
  let outsideArray : Environment → (OutsideIndex ({site} : Finset Lattice) → ℝ) :=
    outsideWeightsAndCocycleIncrements (fun ω : Environment => ω) B {site}
  let mOutside : MeasurableSpace Environment := outsideSigma (fun ω => ω) B {site}
  -- Keep the original environment field active for probability and iid APIs.
  let : MeasurableSpace Environment := mEnvironment

  -- The site and all other sites are disjoint parts of the iid family.
  have hDisjoint : Disjoint siteIndex awayIndex := by
    refine Set.disjoint_left.mpr ?_
    intro z hzSite hzAway
    exact hzAway (by simpa [siteIndex] using hzSite)
  have hArrays :
      IndepFun (fun ω (z : siteIndex) => ω z.1)
        (fun ω (z : awayIndex) => ω z.1) (environmentLaw μ) :=
    ProbabilityBasics.indepFun_restrict_of_iIndepFun
      (environmentLaw μ) (fun z ω => ω z)
      (iIndepFun_environment_eval μ)
      (fun z => measurable_environment_eval z)
      siteIndex awayIndex hDisjoint
  have hSiteEval : Measurable siteEval :=
    measurable_pi_apply (⟨site, by simp [siteIndex]⟩ : siteIndex)
  have hSiteAway : IndepFun X H (environmentLaw μ) := by
    change IndepFun
      (siteEval ∘ (fun ω (z : siteIndex) => ω z.1))
      (fun ω (z : awayIndex) => ω z.1) (environmentLaw μ)
    exact hArrays.comp hSiteEval measurable_id
  have hSiteFunction : X = fun ω : Environment => ω site := by
    funext ω
    simp [X, siteEval, siteIndex]

  -- The whole away array generates a subfield of the ambient environment field.
  have hAwayMeasurable : Measurable H := by
    apply measurable_pi_iff.mpr
    intro z
    exact measurable_environment_eval z.1
  have hAwayLeAmbient : mAway ≤ mEnvironment := by
    change MeasurableSpace.comap H
      (inferInstance : MeasurableSpace (awayIndex → ℝ)) ≤ mEnvironment
    exact hAwayMeasurable.comap_le

  -- If `y` is outside the lower orthant of the site, all sites northeast of `y` differ from it.
  have hForwardLeAway (y : Lattice)
      (hy : y ∈ outsideLowerOrthants ({site} : Finset Lattice)) :
      forwardWeightSigma y ≤ mAway := by
    have hyNotLeSite : ¬ y ≤ site := by
      change ∀ x ∈ ({site} : Finset Lattice), ¬ y ≤ x at hy
      exact hy site (by simp)
    have hNortheastWeights :
        @Measurable Environment ({z : Lattice // y ≤ z} → ℝ)
          mAway inferInstance (fun ω z => ω z.1) := by
      let : MeasurableSpace Environment := mAway
      apply measurable_pi_iff.mpr
      intro z
      have hzNotSite : z.1 ≠ site := by
        intro hz
        apply hyNotLeSite
        simpa [hz] using z.2
      exact (measurable_pi_apply (⟨z.1, hzNotSite⟩ : awayIndex)).comp
        (comap_measurable H)
    simpa only [forwardWeightSigma] using hNortheastWeights.comap_le

  -- Every weight and every required edge increment is measurable in the away field.
  have hOutsideAway :
      @Measurable Environment (OutsideIndex ({site} : Finset Lattice) → ℝ)
        mAway inferInstance outsideArray := by
    let : MeasurableSpace Environment := mAway
    apply measurable_pi_iff.mpr
    intro j
    cases j with
    | inl x =>
        have hxNotSite : x.1 ≠ site := by
          intro hx
          apply x.2
          simp [hx]
        change Measurable (fun ω : Environment => ω x.1)
        exact (measurable_pi_apply (⟨x.1, hxNotSite⟩ : awayIndex)).comp
          (comap_measurable H)
    | inr yi =>
        rcases yi with ⟨y, i⟩
        have hStep : y.1 ≤ y.1 + finiteEdgeStep i := by
          fin_cases i <;> simp [finiteEdgeStep, Prod.le_def]
        have hBForward :
            Measurable[forwardWeightSigma y.1]
              (fun ω : Environment => B y.1 (y.1 + finiteEdgeStep i) ω) :=
          hForward y.1 y.1 (y.1 + finiteEdgeStep i) le_rfl hStep
        have hBAway :
            Measurable[mAway]
              (fun ω : Environment => B y.1 (y.1 + finiteEdgeStep i) ω) :=
          hBForward.mono (hForwardLeAway y.1 y.2) le_rfl
        change Measurable
          (fun ω : Environment => B y.1 (y.1 + finiteEdgeStep i) ω)
        exact hBAway

  -- The outside field is contained in the away field, so it inherits independence.
  have hOutsideLeAway : mOutside ≤ mAway := by
    change MeasurableSpace.comap outsideArray inferInstance ≤ mAway
    exact hOutsideAway.comap_le
  have hFieldIndep : Indep mSite mAway (environmentLaw μ) := by
    change Indep (MeasurableSpace.comap X (inferInstance : MeasurableSpace ℝ))
      (MeasurableSpace.comap H (inferInstance : MeasurableSpace (awayIndex → ℝ)))
      (environmentLaw μ)
    exact (IndepFun_iff_Indep X H (environmentLaw μ)).mp hSiteAway
  have hSiteOutsideIndep : Indep mSite mOutside (environmentLaw μ) :=
    indep_of_indep_of_le hFieldIndep le_rfl hOutsideLeAway
  have hOutsideIndep : IndepFun X outsideArray (environmentLaw μ) :=
    (IndepFun_iff_Indep X outsideArray (environmentLaw μ)).mpr hSiteOutsideIndep
  rw [hSiteFunction] at hOutsideIndep

  -- The common conditional-expectation bridge gives the canonical conclusion.
  exact ae_singleton_outside_condExp_pos_of_indep
    (P := environmentLaw μ) (weights := fun ω : Environment => ω) B site
    (measurable_environment_eval site) (hOutsideAway.mono hAwayLeAmbient le_rfl)
    hOutsideIndep K hMass

/-- An increment measurable from its northeast weights is independent of the
origin event when its root is outside the origin lower orthant. The whole-array
argument uses GRS, arXiv:1510.00860v1, Appendix A, lines 1440–1470, and the
forward measurability condition from Strong Existence, lines 470–475. -/
theorem hasDownwardFiniteEnergy_environmentLaw_of_isForwardMeasurable
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (B : Lattice → Lattice → Environment → ℝ)
    (hForward : IsForwardMeasurable B) :
    HasDownwardFiniteEnergy (environmentLaw μ) (fun ω => ω) B := by

  unfold HasDownwardFiniteEnergy
  exact ae_singleton_outside_condExp_pos_environmentLaw_of_isForwardMeasurable
    μ B hForward 0

end LPP.Busemann
