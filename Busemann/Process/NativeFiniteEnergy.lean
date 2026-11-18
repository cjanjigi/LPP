/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.DownwardFiniteEnergyIndependence
public import Busemann.Process.BackwardIndependence
public import Busemann.Frozen.Definitions.ProcessEnvironment
public import Busemann.Frozen.Definitions.OutsideWeightsAndCocycleIncrements
public import LPP_Foundations.Probability.CoordinateLaw
public import ProbabilityBasics.Probability.DisjointFamilies
public import ProbabilityBasics.Probability.IndependenceReassociation
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-! The native backward-independence clause implies finite energy at the origin. -/

@[expose] public section

open MeasureTheory ProbabilityTheory LPPDifferentiability

namespace LPP.Busemann

/-- For each site, the full native backward-independence clause gives
positive singleton conditional probabilities given the complete outside array,
for either cocycle sign. This is the site version of the probability argument
in JR arXiv:1810.03580v3, Theorem 4.8(b). -/
theorem ae_singleton_outside_condExp_pos_native_family_of_backward_independence
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (g : Quadrant → ℝ) (P : Measure ProcessSample)
    (hP : P Set.univ = 1)
    (Bminus Bplus : SupportTilt g → Lattice → Lattice → ProcessSample → ℝ)
    (hMarginal : P.map processEnvironment = environmentLaw μ)
    (hMeasMinus : Measurable
      (fun q : SupportTilt g × (Lattice × (Lattice × ProcessSample)) =>
        Bminus q.1 q.2.1 q.2.2.1 q.2.2.2))
    (hMeasPlus : Measurable
      (fun q : SupportTilt g × (Lattice × (Lattice × ProcessSample)) =>
        Bplus q.1 q.2.1 q.2.2.1 q.2.2.2))
    (hBackward : HasBackwardIndependence g P Bminus Bplus) :
    ∀ (h : SupportTilt g) (right : Bool),
      let C := if right then Bplus h else Bminus h
      ∀ (z : Lattice) (K : ℝ),
        0 < P {s : ProcessSample | processEnvironment s z ≤ K} →
        ∀ᵐ s ∂P, 0 < (MeasureTheory.condExp
          (outsideSigma processEnvironment C {z}) P
          (Set.indicator {s : ProcessSample | processEnvironment s z ≤ K}
            (fun _ => (1 : ℝ)))) s := by
  classical
  intro h right
  dsimp only
  intro site K hMass
  have hPprob : IsProbabilityMeasure P := ⟨hP⟩

  let I : Set Lattice := {y | ¬ y ≤ site}
  let pastOther : Type := {x : Lattice // x ≤ site ∧ x ≠ site}
  let pastIndex : Type := {x : Lattice // ∀ z ∈ I, ¬ z ≤ x}
  let futureIndex : Type := Sum {x : Lattice // x ∈ I} (FutureCocycleIndex g I)

  have hPastSite : ∀ z ∈ I, ¬ z ≤ site := by
    intro z hz
    exact hz
  have hPastOtherIndex (x : pastOther) : ∀ z ∈ I, ¬ z ≤ x.1 := by
    intro z hz hzx
    exact hz (hzx.trans x.2.1)
  let pastSite : pastIndex := ⟨site, hPastSite⟩
  let pastToPair : (pastIndex → ℝ) → ℝ × (pastOther → ℝ) :=
    fun a => (a pastSite, fun x => a ⟨x.1, hPastOtherIndex x⟩)

  let X : ProcessSample → ℝ := fun s => processEnvironment s site
  let S : ProcessSample → (pastOther → ℝ) :=
    fun s x => processEnvironment s x.1
  let U : ProcessSample → (futureIndex → ℝ) :=
    futureVariables g I Bminus Bplus
  let XS : ProcessSample → ℝ × (pastOther → ℝ) :=
    fun s => (X s, S s)

  -- The past index is exactly the southwest quadrant.
  have hPastToPairMeas : Measurable pastToPair := by
    change Measurable (fun a : pastIndex → ℝ =>
      (a pastSite, fun x => a ⟨x.1, hPastOtherIndex x⟩))
    have hFirst : Measurable (fun a : pastIndex → ℝ => a pastSite) :=
      measurable_pi_apply pastSite
    have hSecond : Measurable
        (fun a : pastIndex → ℝ => fun x => a ⟨x.1, hPastOtherIndex x⟩) := by
      apply measurable_pi_iff.mpr
      intro x
      exact measurable_pi_apply (⟨x.1, hPastOtherIndex x⟩ : pastIndex)
    exact hFirst.prodMk hSecond
  have hPastPair : XS = pastToPair ∘ pastVariables I := by
    funext s
    apply Prod.ext
    · simp [XS, X, pastToPair, pastVariables, processEnvironment, pastSite]
    · funext x
      simp [XS, S, pastToPair, pastVariables, processEnvironment]

  -- The entire future array is measurable in the original sample field.
  have hFutureSection (q : FutureCocycleIndex g I) :
      Measurable (fun s : ProcessSample => (q.tilt, (q.root, (q.target, s)))) :=
    measurable_const.prodMk
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hBminusSection (q : FutureCocycleIndex g I) :
      Measurable (fun s : ProcessSample => Bminus q.tilt q.root q.target s) := by
    have hEq :
        ((fun r : SupportTilt g × (Lattice × (Lattice × ProcessSample)) =>
          Bminus r.1 r.2.1 r.2.2.1 r.2.2.2) ∘
          fun s => (q.tilt, (q.root, (q.target, s)))) =
          (fun s => Bminus q.tilt q.root q.target s) := by
      funext s
      rfl
    exact hEq ▸ hMeasMinus.comp (hFutureSection q)
  have hBplusSection (q : FutureCocycleIndex g I) :
      Measurable (fun s : ProcessSample => Bplus q.tilt q.root q.target s) := by
    have hEq :
        ((fun r : SupportTilt g × (Lattice × (Lattice × ProcessSample)) =>
          Bplus r.1 r.2.1 r.2.2.1 r.2.2.2) ∘
          fun s => (q.tilt, (q.root, (q.target, s)))) =
          (fun s => Bplus q.tilt q.root q.target s) := by
      funext s
      rfl
    exact hEq ▸ hMeasPlus.comp (hFutureSection q)
  have hXMeas : Measurable X :=
    (measurable_environment_eval site).comp measurable_fst
  have hSMeas : Measurable S := by
    apply measurable_pi_iff.mpr
    intro x
    change Measurable (fun s : ProcessSample => processEnvironment s x.1)
    have hEq :
        ((fun ω : Environment => ω x.1) ∘ (fun s : ProcessSample => s.1)) =
          (fun s : ProcessSample => processEnvironment s x.1) := by
      funext s
      rfl
    exact hEq ▸ (measurable_environment_eval x.1).comp measurable_fst
  have hUMeas : Measurable U := by
    apply measurable_pi_iff.mpr
    intro j
    cases j with
    | inl x =>
        change Measurable (fun s : ProcessSample => processEnvironment s x.1)
        have hEq :
            ((fun ω : Environment => ω x.1) ∘ (fun s : ProcessSample => s.1)) =
              (fun s : ProcessSample => processEnvironment s x.1) := by
          funext s
          rfl
        exact hEq ▸ (measurable_environment_eval x.1).comp measurable_fst
    | inr q =>
        by_cases hright : q.right
        · simpa [U, futureVariables, hright] using
            hBplusSection q
        · simpa [U, futureVariables, hright] using
            hBminusSection q

  -- The backward clause makes the site and southwest block independent of all future data.
  have hBackwardPast : IndepFun (pastVariables I) U P :=
    (show IndepFun U (pastVariables I) P from hBackward I).symm
  have hBlock : IndepFun XS U P := by
    rw [hPastPair]
    exact hBackwardPast.comp hPastToPairMeas measurable_id

  -- The iid marginal makes the site independent of the other southwest weights.
  let siteSet : Set Lattice := {site}
  let siteIndex : Type := {x : Lattice // x ∈ siteSet}
  let siteEval : (siteIndex → ℝ) → ℝ :=
    fun a => a ⟨site, by simp [siteSet]⟩
  let siteArray : Environment → (siteIndex → ℝ) :=
    fun ω x => ω x.1
  let XEnv : Environment → ℝ := siteEval ∘ siteArray
  let SEnv : Environment → (pastOther → ℝ) := fun ω x => ω x.1
  let envPair : Environment → ℝ × (pastOther → ℝ) :=
    fun ω => (XEnv ω, SEnv ω)

  have hDisjoint : Disjoint siteSet {x : Lattice | x ≤ site ∧ x ≠ site} := by
    refine Set.disjoint_left.mpr ?_
    intro x hxSite hxOther
    apply hxOther.2
    simpa [siteSet] using hxSite
  have hEnvArrays : IndepFun
      (fun ω (x : siteIndex) => ω x.1)
      (fun ω (x : pastOther) => ω x.1) (environmentLaw μ) :=
    ProbabilityBasics.indepFun_restrict_of_iIndepFun
      (environmentLaw μ) (fun x ω => ω x)
      (iIndepFun_environment_eval μ)
      (fun x => measurable_environment_eval x)
      siteSet {x : Lattice | x ≤ site ∧ x ≠ site} hDisjoint
  have hSiteEvalMeas : Measurable siteEval :=
    measurable_pi_apply (⟨site, by simp [siteSet]⟩ : siteIndex)
  have hSiteArrayMeas : Measurable siteArray := by
    apply measurable_pi_iff.mpr
    intro x
    exact measurable_environment_eval x.1
  have hXEnvMeas : Measurable XEnv := hSiteEvalMeas.comp hSiteArrayMeas
  have hSEnvMeas : Measurable SEnv := by
    apply measurable_pi_iff.mpr
    intro x
    exact measurable_environment_eval x.1
  have hEnvIndep : IndepFun XEnv SEnv (environmentLaw μ) := by
    change IndepFun
      (siteEval ∘ (fun ω (x : siteIndex) => ω x.1))
      (fun ω (x : pastOther) => ω x.1) (environmentLaw μ)
    exact hEnvArrays.comp hSiteEvalMeas measurable_id
  have hEnvPairMeas : Measurable envPair := hXEnvMeas.prodMk hSEnvMeas
  have hXComp : X = XEnv ∘ processEnvironment := by
    funext s
    simp [X, XEnv, siteEval, siteArray, siteSet, processEnvironment]
  have hSComp : S = SEnv ∘ processEnvironment := by
    funext s
    funext x
    rfl
  have hXSComp : XS = envPair ∘ processEnvironment := by
    funext s
    change (X s, S s) = (XEnv (processEnvironment s), SEnv (processEnvironment s))
    exact Prod.ext (congrFun hXComp s) (congrFun hSComp s)
  have hXMap : P.map X = (environmentLaw μ).map XEnv := by
    calc
      P.map X = P.map (XEnv ∘ processEnvironment) :=
        congrArg (fun f : ProcessSample → ℝ => P.map f) hXComp
      _ = (P.map processEnvironment).map XEnv :=
        (Measure.map_map hXEnvMeas measurable_fst).symm
      _ = (environmentLaw μ).map XEnv := by rw [hMarginal]
  have hSMap : P.map S = (environmentLaw μ).map SEnv := by
    calc
      P.map S = P.map (SEnv ∘ processEnvironment) :=
        congrArg (fun f : ProcessSample → (pastOther → ℝ) => P.map f) hSComp
      _ = (P.map processEnvironment).map SEnv :=
        (Measure.map_map hSEnvMeas measurable_fst).symm
      _ = (environmentLaw μ).map SEnv := by rw [hMarginal]
  have hPairMap : P.map XS = (environmentLaw μ).map envPair := by
    calc
      P.map XS = P.map (envPair ∘ processEnvironment) :=
        congrArg (fun f : ProcessSample → ℝ × (pastOther → ℝ) => P.map f) hXSComp
      _ = (P.map processEnvironment).map envPair :=
        (Measure.map_map hEnvPairMeas measurable_fst).symm
      _ = (environmentLaw μ).map envPair := by rw [hMarginal]
  have hEnvJoint : (environmentLaw μ).map envPair =
      ((environmentLaw μ).map XEnv).prod ((environmentLaw μ).map SEnv) :=
    (indepFun_iff_map_prod_eq_prod_map_map
      hXEnvMeas.aemeasurable hSEnvMeas.aemeasurable).mp hEnvIndep
  have hXS : IndepFun X S P := by
    apply (indepFun_iff_map_prod_eq_prod_map_map
      hXMeas.aemeasurable hSMeas.aemeasurable).2
    calc
      P.map XS = (environmentLaw μ).map envPair := hPairMap
      _ = ((environmentLaw μ).map XEnv).prod ((environmentLaw μ).map SEnv) := hEnvJoint
      _ = (P.map X).prod (P.map S) := by rw [← hXMap, ← hSMap]

  -- Reassociate the full southwest/future block independence.
  have hXSU : IndepFun X (fun s => (S s, U s)) P :=
    ProbabilityBasics.indepFun_prodMk_right_of_indepFun_prodMk_left
      hXMeas hSMeas hUMeas hBlock hXS

  -- Each actual outside array is a measurable projection of the southwest and future blocks.
  have hStep (y : Lattice) (i : Fin 2) :
      y ≤ y + finiteEdgeStep i := by
    fin_cases i <;> simp [finiteEdgeStep, Prod.le_def]
  have hRootInI (y : Lattice)
      (hy : y ∈ outsideLowerOrthants ({site} : Finset Lattice)) : y ∈ I := by
    change ∀ x ∈ ({site} : Finset Lattice), ¬ y ≤ x at hy
    exact hy site (by simp)
  let unitIndex (h : SupportTilt g) (right : Bool) (y : Lattice)
      (hy : y ∈ outsideLowerOrthants ({site} : Finset Lattice)) (i : Fin 2) :
      FutureCocycleIndex g I :=
    ⟨y, hRootInI y hy, y + finiteEdgeStep i, hStep y i, h, right⟩
  let BFor (right : Bool) (h : SupportTilt g) :
      Lattice → Lattice → ProcessSample → ℝ :=
    if right then Bplus h else Bminus h
  let outsideArray (right : Bool) (h : SupportTilt g) :
      ProcessSample → (OutsideIndex ({site} : Finset Lattice) → ℝ) :=
    outsideWeightsAndCocycleIncrements processEnvironment (BFor right h) {site}
  let outsideFromBlocks (h : SupportTilt g) (right : Bool) :
      (pastOther → ℝ) × (futureIndex → ℝ) →
        (OutsideIndex ({site} : Finset Lattice) → ℝ) :=
    fun p j => match j with
      | .inl x =>
          if hx : x.1 ≤ site then
            p.1 ⟨x.1, hx, by
              intro hxsite
              apply x.2
              simp [hxsite]⟩
          else
            p.2 (Sum.inl ⟨x.1, by simpa [I] using hx⟩)
      | .inr yi =>
          p.2 (Sum.inr (unitIndex h right yi.1.1 yi.1.2 yi.2))

  have hFactorMeas (h : SupportTilt g) (right : Bool) :
      Measurable (outsideFromBlocks h right) := by
    apply measurable_pi_iff.mpr
    intro j
    cases j with
    | inl x =>
        by_cases hx : x.1 ≤ site
        · have hxne : x.1 ≠ site := by
            intro hxsite
            apply x.2
            simp [hxsite]
          simp only [outsideFromBlocks, dite_eq_left hx]
          exact (measurable_pi_apply (⟨x.1, hx, hxne⟩ : pastOther)).comp measurable_fst
        · simp only [outsideFromBlocks, dite_eq_right hx]
          exact (measurable_pi_apply
            (Sum.inl ⟨x.1, by simpa [I] using hx⟩ : futureIndex)).comp measurable_snd
    | inr yi =>
        change Measurable (fun p : (pastOther → ℝ) × (futureIndex → ℝ) =>
          p.2 (Sum.inr (unitIndex h right yi.1.1 yi.1.2 yi.2)))
        exact (measurable_pi_apply
          (Sum.inr (unitIndex h right yi.1.1 yi.1.2 yi.2))).comp measurable_snd

  have hOutsideFactor (h : SupportTilt g) (right : Bool) :
      outsideArray right h = outsideFromBlocks h right ∘ (fun s => (S s, U s)) := by
    funext s
    funext j
    cases j with
    | inl x =>
        by_cases hx : x.1 ≤ site
        · simp [outsideArray, outsideWeightsAndCocycleIncrements,
            outsideFromBlocks, S, processEnvironment, hx]
        · simp [outsideArray, outsideWeightsAndCocycleIncrements,
            outsideFromBlocks, U, futureVariables, processEnvironment, hx, I]
    | inr yi =>
        cases right <;> rfl

  have hOutsideMeas (h : SupportTilt g) (right : Bool) :
      Measurable (outsideArray right h) := by
    rw [hOutsideFactor h right]
    exact (hFactorMeas h right).comp (hSMeas.prodMk hUMeas)
  have hOutsideIndep (h : SupportTilt g) (right : Bool) :
      IndepFun X (outsideArray right h) P := by
    rw [hOutsideFactor h right]
    exact hXSU.comp measurable_id (hFactorMeas h right)

  have hSiteMeas : Measurable (fun s : ProcessSample => processEnvironment s site) :=
    (measurable_environment_eval site).comp measurable_fst
  -- The singleton criterion applies at the chosen site and threshold.
  simpa only [BFor] using
    (ae_singleton_outside_condExp_pos_of_indep
      P processEnvironment (BFor right h) site hSiteMeas
      (hOutsideMeas h right) (hOutsideIndep h right) K hMass)

/-- The full backward-independence clause gives downward finite energy for
every native support tilt and both cocycle signs. This is the probability
argument in Janjigian and Rassoul-Agha, arXiv:1810.03580v3,
Theorem 4.8(b). -/
theorem hasDownwardFiniteEnergy_native_family_of_backward_independence
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (g : Quadrant → ℝ) (P : Measure ProcessSample)
    (hP : P Set.univ = 1)
    (Bminus Bplus : SupportTilt g → Lattice → Lattice → ProcessSample → ℝ)
    (hMarginal : P.map processEnvironment = environmentLaw μ)
    (hMeasMinus : Measurable
      (fun q : SupportTilt g × (Lattice × (Lattice × ProcessSample)) =>
        Bminus q.1 q.2.1 q.2.2.1 q.2.2.2))
    (hMeasPlus : Measurable
      (fun q : SupportTilt g × (Lattice × (Lattice × ProcessSample)) =>
        Bplus q.1 q.2.1 q.2.2.1 q.2.2.2))
    (hBackward : HasBackwardIndependence g P Bminus Bplus) :
    ∀ h : SupportTilt g,
      HasDownwardFiniteEnergy P processEnvironment (Bminus h) ∧
      HasDownwardFiniteEnergy P processEnvironment (Bplus h) := by

  intro h
  constructor
  · unfold HasDownwardFiniteEnergy
    simpa using
      (ae_singleton_outside_condExp_pos_native_family_of_backward_independence
        μ g P hP Bminus Bplus hMarginal hMeasMinus hMeasPlus hBackward h false 0)
  · unfold HasDownwardFiniteEnergy
    simpa using
      (ae_singleton_outside_condExp_pos_native_family_of_backward_independence
        μ g P hP Bminus Bplus hMarginal hMeasMinus hMeasPlus hBackward h true 0)

end LPP.Busemann
