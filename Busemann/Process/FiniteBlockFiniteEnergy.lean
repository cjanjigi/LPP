/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.NativeFiniteEnergy
public import Busemann.Process.ForwardFiniteEnergy
public import Busemann.Process.OutsideFieldMeasurability
public import LPP_Foundations.Probability.CoordinateLaw
public import ProbabilityBasics.Probability.FiniteConditionalPositive
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-! Finite blocks inherit positive conditional probabilities from their sites. -/

@[expose] public section

open MeasureTheory ProbabilityTheory LPPDifferentiability

namespace LPP.Busemann

/-- For the native family, every finite block of weights has positive
conditional probability given its complete outside field, for either cocycle
sign and every support tilt. This is the finite-block induction in GRS,
arXiv:1510.00860v1, Appendix A.2, lines 1441–1474. -/
theorem ae_finset_outside_condExp_pos_native_family_of_backward_independence
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
    (hBackward : ∀ I : Set Lattice,
      IndepFun (futureVariables g I Bminus Bplus) (pastVariables I) P) :
    ∀ (h : SupportTilt g) (right : Bool),
      let C := if right then Bplus h else Bminus h
      ∀ (K : ℝ), 0 < μ (Set.Iic K) →
        ∀ V : Finset Lattice, ∀ᵐ s ∂P,
          0 < (MeasureTheory.condExp (outsideSigma processEnvironment C V) P
            (Set.indicator
              {s : ProcessSample | ∀ z ∈ V, processEnvironment s z ≤ K}
              (fun _ => (1 : ℝ)))) s := by
  classical
  let : IsProbabilityMeasure P := ⟨hP⟩
  intro h right
  dsimp only
  intro K hK V
  let C : Lattice → Lattice → ProcessSample → ℝ :=
    if right then Bplus h else Bminus h
  let m (W : Finset Lattice) : MeasurableSpace ProcessSample :=
    outsideSigma processEnvironment C W
  let E (z : Lattice) : Set ProcessSample :=
    {s : ProcessSample | processEnvironment s z ≤ K}

  -- Fixing the tilt and both endpoints gives measurable native cocycle sections.
  have hSection (x y : Lattice) :
      Measurable (fun s : ProcessSample => (h, (x, (y, s)))) :=
    measurable_const.prodMk
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hMinusSection (x y : Lattice) :
      Measurable (fun s : ProcessSample => Bminus h x y s) := by
    have hEq :
        ((fun q : SupportTilt g × (Lattice × (Lattice × ProcessSample)) =>
          Bminus q.1 q.2.1 q.2.2.1 q.2.2.2) ∘
          (fun s => (h, (x, (y, s))))) =
          (fun s => Bminus h x y s) := by
      funext s
      rfl
    exact hEq ▸ hMeasMinus.comp (hSection x y)
  have hPlusSection (x y : Lattice) :
      Measurable (fun s : ProcessSample => Bplus h x y s) := by
    have hEq :
        ((fun q : SupportTilt g × (Lattice × (Lattice × ProcessSample)) =>
          Bplus q.1 q.2.1 q.2.2.1 q.2.2.2) ∘
          (fun s => (h, (x, (y, s))))) =
          (fun s => Bplus h x y s) := by
      funext s
      rfl
    exact hEq ▸ hMeasPlus.comp (hSection x y)
  have hCMeas (x y : Lattice) :
      Measurable (fun s : ProcessSample => C x y s) := by
    dsimp only [C]
    by_cases hright : right
    · simpa [hright] using hPlusSection x y
    · simpa [hright] using hMinusSection x y

  -- Each native site has the prescribed one-dimensional marginal law.
  have hWeightMeas (z : Lattice) :
      Measurable (fun s : ProcessSample => processEnvironment s z) :=
    (measurable_environment_eval z).comp measurable_fst
  have hSiteMap (z : Lattice) :
      P.map (fun s : ProcessSample => processEnvironment s z) = μ := by
    calc
      P.map (fun s : ProcessSample => processEnvironment s z) =
          (P.map processEnvironment).map (fun ω : Environment => ω z) :=
        (Measure.map_map (measurable_environment_eval z) measurable_fst).symm
      _ = (environmentLaw μ).map (fun ω : Environment => ω z) := by
        rw [hMarginal]
      _ = μ := environmentLaw_map_eval μ z
  have hSiteEventMap (z : Lattice) :
      P {s : ProcessSample | processEnvironment s z ≤ K} =
        (P.map (fun s : ProcessSample => processEnvironment s z)) (Set.Iic K) := by
    calc
      P {s : ProcessSample | processEnvironment s z ≤ K} =
          P ((fun s : ProcessSample => processEnvironment s z) ⁻¹' Set.Iic K) := rfl
      _ = (P.map (fun s : ProcessSample => processEnvironment s z)) (Set.Iic K) :=
        (Measure.map_apply (hWeightMeas z) measurableSet_Iic).symm
  have hSitePos (z : Lattice) :
      0 < P {s : ProcessSample | processEnvironment s z ≤ K} := by
    rw [hSiteEventMap z, hSiteMap z]
    exact hK

  -- The fields are nested, and every outside site event is measurable.
  have hm (W : Finset Lattice) :
      m W ≤ (inferInstance : MeasurableSpace ProcessSample) := by
    change outsideSigma processEnvironment C W ≤ _
    exact outsideSigma_le processEnvironment C W hWeightMeas hCMeas
  have hmono (U W : Finset Lattice) (hUW : U ⊆ W) : m W ≤ m U := by
    exact outsideSigma_antitone processEnvironment C hUW
  have hE (z : Lattice) :
      @MeasurableSet ProcessSample (inferInstance : MeasurableSpace ProcessSample)
        (E z) := by
    change MeasurableSet {s : ProcessSample | processEnvironment s z ≤ K}
    exact measurableSet_le (hWeightMeas z) measurable_const
  have hOutside (z w : Lattice) (hzw : z ≠ w) :
      @MeasurableSet ProcessSample (m {z}) (E w) := by
    let : MeasurableSpace ProcessSample := m {z}
    have hw : w ∉ ({z} : Finset Lattice) := by
      simp only [Finset.mem_singleton]
      exact hzw.symm
    change MeasurableSet {s : ProcessSample | processEnvironment s w ≤ K}
    exact measurableSet_le
      (measurable_outside_weight processEnvironment C {z} w hw)
      measurable_const

  -- The existing all-site conditional-expectation result supplies each block factor.
  have hSingle (z : Lattice) :
      ∀ᵐ s ∂P, 0 < (MeasureTheory.condExp (m {z}) P
        ((E z).indicator fun _ : ProcessSample => (1 : ℝ))) s := by
    simpa [m, E, C] using
      (ae_singleton_outside_condExp_pos_native_family_of_backward_independence
        μ g P hP Bminus Bplus hMarginal hMeasMinus hMeasPlus hBackward
        h right z K (hSitePos z))

  -- The finite induction gives the exact displayed block event.
  have hBlockEvent : (⋂ z ∈ V, E z) =
      {s : ProcessSample | ∀ z ∈ V, processEnvironment s z ≤ K} := by
    ext s
    simp [E]
  have hFinitePos := ProbabilityBasics.ae_condExp_indicator_finset_pos
    P m hm hmono E hE hOutside hSingle V
  rw [hBlockEvent] at hFinitePos
  simpa [m, E, C] using hFinitePos

/-- Under forward measurability, every finite block of the canonical iid
environment has positive conditional probability given its complete outside
field. This is the finite-block induction in GRS, arXiv:1510.00860v1,
Appendix A.2, lines 1441–1474. -/
theorem ae_finset_outside_condExp_pos_environmentLaw_of_isForwardMeasurable
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (B : Lattice → Lattice → Environment → ℝ)
    (hForward : IsForwardMeasurable B) :
    ∀ (K : ℝ), 0 < μ (Set.Iic K) →
      ∀ V : Finset Lattice, ∀ᵐ ω ∂environmentLaw μ,
        0 < (MeasureTheory.condExp
          (outsideSigma (fun ω : Environment => ω) B V) (environmentLaw μ)
          (Set.indicator {ω : Environment | ∀ z ∈ V, ω z ≤ K}
            (fun _ => (1 : ℝ)))) ω := by
  classical
  intro K hK V
  let m (W : Finset Lattice) : MeasurableSpace Environment :=
    outsideSigma (fun ω : Environment => ω) B W
  let E (z : Lattice) : Set Environment := {ω : Environment | ω z ≤ K}

  -- Every forward cone is contained in the original environment field.
  have hForwardFieldLeAmbient (u : Lattice) :
      forwardWeightSigma u ≤ (inferInstance : MeasurableSpace Environment) := by
    have hConeMeas :
        Measurable (fun ω : Environment => fun z : {x : Lattice // u ≤ x} => ω z.1) := by
      apply measurable_pi_iff.mpr
      intro z
      exact measurable_environment_eval z.1
    simpa only [forwardWeightSigma] using hConeMeas.comap_le
  have hBMeas (x y : Lattice) :
      Measurable (fun ω : Environment => B x y ω) := by
    let u : Lattice := x ⊓ y
    have huX : u ≤ x := by dsimp [u]; exact inf_le_left
    have huY : u ≤ y := by dsimp [u]; exact inf_le_right
    exact (hForward u x y huX huY).mono (hForwardFieldLeAmbient u) le_rfl

  -- The full outside field lies in the unchanged environment field.
  have hm (W : Finset Lattice) :
      m W ≤ (inferInstance : MeasurableSpace Environment) := by
    change outsideSigma (fun ω : Environment => ω) B W ≤ _
    exact outsideSigma_le (fun ω : Environment => ω) B W
      (fun z => measurable_environment_eval z) hBMeas
  have hmono (U W : Finset Lattice) (hUW : U ⊆ W) : m W ≤ m U := by
    exact outsideSigma_antitone (fun ω : Environment => ω) B hUW
  have hE (z : Lattice) :
      @MeasurableSet Environment (inferInstance : MeasurableSpace Environment)
        (E z) := by
    change MeasurableSet {ω : Environment | ω z ≤ K}
    exact measurableSet_le (measurable_environment_eval z) measurable_const
  have hOutside (z w : Lattice) (hzw : z ≠ w) :
      @MeasurableSet Environment (m {z}) (E w) := by
    let : MeasurableSpace Environment := m {z}
    have hw : w ∉ ({z} : Finset Lattice) := by
      simp only [Finset.mem_singleton]
      exact hzw.symm
    change MeasurableSet {ω : Environment | ω w ≤ K}
    exact measurableSet_le
      (measurable_outside_weight (fun ω : Environment => ω) B {z} w hw)
      measurable_const

  -- The coordinate law gives the positive mass required by every singleton producer.
  have hEnvironmentEventMap (z : Lattice) :
      (environmentLaw μ) {ω : Environment | ω z ≤ K} =
        ((environmentLaw μ).map (fun ω : Environment => ω z)) (Set.Iic K) := by
    calc
      (environmentLaw μ) {ω : Environment | ω z ≤ K} =
          (environmentLaw μ) ((fun ω : Environment => ω z) ⁻¹' Set.Iic K) := rfl
      _ = ((environmentLaw μ).map (fun ω : Environment => ω z)) (Set.Iic K) :=
        (Measure.map_apply (measurable_environment_eval z)
          measurableSet_Iic).symm
  have hSitePos (z : Lattice) :
      0 < (environmentLaw μ) {ω : Environment | ω z ≤ K} := by
    rw [hEnvironmentEventMap z, environmentLaw_map_eval μ z]
    exact hK
  have hSingle (z : Lattice) :
      ∀ᵐ ω ∂environmentLaw μ, 0 < (MeasureTheory.condExp (m {z})
        (environmentLaw μ) ((E z).indicator fun _ : Environment => (1 : ℝ))) ω := by
    simpa [m, E] using
      (ae_singleton_outside_condExp_pos_environmentLaw_of_isForwardMeasurable
        μ B hForward z K (hSitePos z))

  -- The same finite induction returns the original block event, even when it is empty.
  have hBlockEvent : (⋂ z ∈ V, E z) =
      {ω : Environment | ∀ z ∈ V, ω z ≤ K} := by
    ext ω
    simp [E]
  have hFinitePos := ProbabilityBasics.ae_condExp_indicator_finset_pos
    (environmentLaw μ) m hm hmono E hE hOutside hSingle V
  rw [hBlockEvent] at hFinitePos
  simpa [m, E] using hFinitePos

end LPP.Busemann
