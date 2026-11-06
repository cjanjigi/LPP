/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.BilateralJointAverages
public import Martin2004.Probability.BilateralJointCoupling
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.Order.LiminfLimsup

/-! # The centered upper bound from one joint majorant

The actual array's one-sided constant limit identifies the increment limit
under the same joint law. The centered interval comparison then projects to
the array law. No ergodicity of the joint extension is assumed.
-/

public section

open MeasureTheory Filter
open scoped Topology BigOperators

namespace LPPDifferentiability

/-- The original positive origin-interval limit is a measurable array event. -/
theorem measurableSet_bilateralArray_forward_tendsto (q : ℝ) :
    MeasurableSet {x : BilateralArray | Tendsto (fun n : ℕ =>
      x ⟨(0, (n + 1 : ℕ)), by omega⟩ / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 q)} :=
  measurableSet_tendsto_fun
    (fun n => (measurable_pi_apply (⟨(0, (n + 1 : ℕ)), by omega⟩ : BilateralInterval)).div_const _)
    measurable_const

/-- The actual centered extended-real upper bound is a measurable array event. -/
theorem measurableSet_bilateralArray_centered_limsup_le (q : ℝ) :
    MeasurableSet {x : BilateralArray |
      limsup (fun n : ℕ => ((x ⟨(-((n + 1 : ℕ) : ℤ), (n + 1 : ℕ)), by omega⟩ /
        (2 * ((n + 1 : ℕ) : ℝ)) : ℝ) : EReal)) atTop ≤ (q : EReal)} := by
  have hm (n : ℕ) : Measurable (fun x : BilateralArray =>
      x ⟨(-((n + 1 : ℕ) : ℤ), (n + 1 : ℕ)), by omega⟩ /
        (2 * ((n + 1 : ℕ) : ℝ))) :=
    (measurable_pi_apply _).div_const _
  exact measurableSet_le (Measurable.limsup fun n => (hm n).coe_real_ereal) measurable_const

/-- All-interval majorization gives actual positive forward domination. -/
theorem bilateralArray_forward_div_le_birkhoffAverage
    (p : BilateralJoint)
    (hmajor : ∀ v : BilateralInterval,
      p.1 v ≤ ∑ t ∈ Finset.Ico v.1.1 v.1.2, p.2 t)
    (n : ℕ) (hn : 0 < n) :
    p.1 ⟨(0, (n : ℤ)), by omega⟩ / (n : ℝ) ≤
      birkhoffAverage ℝ bilateralJointShiftMeasurableEquiv
        (fun p : BilateralJoint => p.2 0) n p := by
  rw [birkhoffAverage_bilateralJointShift_snd_zero_eq_sum]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  have h := hmajor ⟨(0, (n : ℤ)), by omega⟩
  simpa only [Int.Ico_eq_finset_map, Finset.sum_map, sub_zero,
    Int.toNat_natCast, Function.Embedding.trans_apply, Nat.castEmbedding_apply,
    addLeftEmbedding_apply, zero_add] using h

/-- The same joint majorant has forward and centered increment limits q,
almost surely and in L1. The observable is the actual coordinate z(0). -/
theorem bilateralJoint_forward_centered_tendsto_const
    (ρ : ProbabilityMeasure BilateralArray) (ν : ProbabilityMeasure BilateralJoint)
    (hfst : MeasurePreserving Prod.fst (ν : Measure BilateralJoint)
      (ρ : Measure BilateralArray))
    (hT : MeasurePreserving bilateralJointShiftMeasurableEquiv
      (ν : Measure BilateralJoint) (ν : Measure BilateralJoint))
    (hi : Integrable (fun p : BilateralJoint => p.2 0) (ν : Measure BilateralJoint))
    (q : ℝ) (hmean : (∫ p, p.2 0 ∂(ν : Measure BilateralJoint)) ≤ q)
    (hmajor : ∀ᵐ p ∂(ν : Measure BilateralJoint), ∀ v : BilateralInterval,
      p.1 v ≤ ∑ t ∈ Finset.Ico v.1.1 v.1.2, p.2 t)
    (hforward : ∀ᵐ x ∂(ρ : Measure BilateralArray), Tendsto (fun n : ℕ =>
      x ⟨(0, (n + 1 : ℕ)), by omega⟩ / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 q)) :
    ((∀ᵐ p ∂(ν : Measure BilateralJoint), Tendsto (fun n : ℕ =>
        birkhoffAverage ℝ bilateralJointShiftMeasurableEquiv
          (fun p : BilateralJoint => p.2 0) n p) atTop (𝓝 q)) ∧
      Tendsto (fun n : ℕ => ∫ p,
        |birkhoffAverage ℝ bilateralJointShiftMeasurableEquiv
          (fun p : BilateralJoint => p.2 0) n p - q| ∂(ν : Measure BilateralJoint))
        atTop (𝓝 0)) ∧
    ((∀ᵐ p ∂(ν : Measure BilateralJoint), Tendsto (fun n : ℕ =>
        centeredBirkhoffAverage bilateralJointShiftMeasurableEquiv
          (fun p : BilateralJoint => p.2 0) n p) atTop (𝓝 q)) ∧
      Tendsto (fun n : ℕ => ∫ p,
        |centeredBirkhoffAverage bilateralJointShiftMeasurableEquiv
          (fun p : BilateralJoint => p.2 0) n p - q| ∂(ν : Measure BilateralJoint))
        atTop (𝓝 0)) := by
  have hforwardν : ∀ᵐ p ∂(ν : Measure BilateralJoint), Tendsto (fun n : ℕ =>
      p.1 ⟨(0, (n + 1 : ℕ)), by omega⟩ / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 q) := by
    apply (ae_map_iff measurable_fst.aemeasurable
      (measurableSet_bilateralArray_forward_tendsto q)).mp
    rwa [hfst.map_eq]
  let A : ℕ → BilateralJoint → ℝ := fun n p =>
    match n with
    | 0 => 0
    | k + 1 => p.1 ⟨(0, (k + 1 : ℕ)), by omega⟩
  have hA : ∀ᵐ p ∂(ν : Measure BilateralJoint),
      Tendsto (fun n : ℕ => A n p / (n : ℝ)) atTop (𝓝 q) := by
    filter_upwards [hforwardν] with p hp
    exact (tendsto_add_atTop_iff_nat 1).mp hp
  have hdom : ∀ᵐ p ∂(ν : Measure BilateralJoint), ∀ n : ℕ, 0 < n →
      A n p / (n : ℝ) ≤ birkhoffAverage ℝ bilateralJointShiftMeasurableEquiv
        (fun p : BilateralJoint => p.2 0) n p := by
    filter_upwards [hmajor] with p hp
    intro n hn
    cases n with
    | zero => omega
    | succ k => exact bilateralArray_forward_div_le_birkhoffAverage p hp (k + 1) hn
  exact forward_centeredBirkhoffAverage_tendsto_const_of_dominated_sequence
    hT ((measurable_pi_apply 0).comp measurable_snd) hi hmean hA hdom

/-- One joint stationary interval majorant proves the centered upper bound
under its original array marginal. No centered lower bound is a premise. -/
theorem ae_bilateralArray_centered_limsup_le_of_joint_majorant
    (ρ : ProbabilityMeasure BilateralArray) (ν : ProbabilityMeasure BilateralJoint)
    (hfst : MeasurePreserving Prod.fst (ν : Measure BilateralJoint)
      (ρ : Measure BilateralArray))
    (hT : MeasurePreserving bilateralJointShiftMeasurableEquiv
      (ν : Measure BilateralJoint) (ν : Measure BilateralJoint))
    (hi : Integrable (fun p : BilateralJoint => p.2 0) (ν : Measure BilateralJoint))
    (q : ℝ) (hmean : (∫ p, p.2 0 ∂(ν : Measure BilateralJoint)) ≤ q)
    (hmajor : ∀ᵐ p ∂(ν : Measure BilateralJoint), ∀ v : BilateralInterval,
      p.1 v ≤ ∑ t ∈ Finset.Ico v.1.1 v.1.2, p.2 t)
    (hforward : ∀ᵐ x ∂(ρ : Measure BilateralArray), Tendsto (fun n : ℕ =>
      x ⟨(0, (n + 1 : ℕ)), by omega⟩ / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 q)) :
    ∀ᵐ x ∂(ρ : Measure BilateralArray),
      limsup (fun n : ℕ => ((x ⟨(-((n + 1 : ℕ) : ℤ), (n + 1 : ℕ)), by omega⟩ /
        (2 * ((n + 1 : ℕ) : ℝ)) : ℝ) : EReal)) atTop ≤ (q : EReal) := by
  have hcentered := (bilateralJoint_forward_centered_tendsto_const
    ρ ν hfst hT hi q hmean hmajor hforward).2.1
  rw [← hfst.map_eq]
  apply (ae_map_iff measurable_fst.aemeasurable
    (measurableSet_bilateralArray_centered_limsup_le q)).mpr
  filter_upwards [hcentered, hmajor] with p hp hm
  have hlim := EReal.tendsto_coe.mpr (hp.comp (tendsto_add_atTop_nat 1))
  calc
    _ ≤ limsup (fun n : ℕ => ((centeredBirkhoffAverage
        bilateralJointShiftMeasurableEquiv (fun p : BilateralJoint => p.2 0)
        (n + 1) p : ℝ) : EReal)) atTop := by
      refine limsup_le_limsup (Eventually.of_forall fun n => ?_)
        (isCoboundedUnder_le_of_le _ fun _ => bot_le)
        (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)
      apply EReal.coe_le_coe_iff.mpr
      rw [centeredBirkhoffAverage_bilateralJointShift_snd_zero_eq_sum]
      exact div_le_div_of_nonneg_right
        (hm ⟨(-((n + 1 : ℕ) : ℤ), (n + 1 : ℕ)), by omega⟩) (by positivity)
    _ = (q : EReal) := hlim.limsup_eq

/-- Pull the measurable centered upper event back through the actual array
map. The exact pushforward identity keeps the original probability space. -/
theorem ae_bilateralArray_centered_limsup_le_comp
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Q : Ω → BilateralArray) (hQ : Measurable Q)
    (ρ : ProbabilityMeasure BilateralArray)
    (hρ : μ.map Q = (ρ : Measure BilateralArray)) (q : ℝ)
    (hu : ∀ᵐ x ∂(ρ : Measure BilateralArray),
      limsup (fun n : ℕ => ((x ⟨(-((n + 1 : ℕ) : ℤ), (n + 1 : ℕ)), by omega⟩ /
        (2 * ((n + 1 : ℕ) : ℝ)) : ℝ) : EReal)) atTop ≤ (q : EReal)) :
    ∀ᵐ ω ∂μ,
      limsup (fun n : ℕ => (((Q ω) ⟨(-((n + 1 : ℕ) : ℤ), (n + 1 : ℕ)), by omega⟩ /
        (2 * ((n + 1 : ℕ) : ℝ)) : ℝ) : EReal)) atTop ≤ (q : EReal) := by
  apply (ae_map_iff hQ.aemeasurable
    (measurableSet_bilateralArray_centered_limsup_le q)).mp
  rwa [hρ]

/-- The finite stationary nonnegative superadditive array hypotheses produce
the joint majorant internally. Its sharp expected rate is the same supplied
one-sided rate, even when the finite upper bound B is slack. -/
theorem ae_bilateralArray_centered_limsup_le
    (ρ : ProbabilityMeasure BilateralArray)
    (hS : MeasurePreserving bilateralArrayShift
      (ρ : Measure BilateralArray) (ρ : Measure BilateralArray))
    (hi : ∀ v : BilateralInterval,
      Integrable (fun x : BilateralArray => x v) (ρ : Measure BilateralArray))
    (hnonneg : ∀ᵐ x ∂(ρ : Measure BilateralArray), ∀ v, 0 ≤ x v)
    (hadd : ∀ᵐ x ∂(ρ : Measure BilateralArray),
      ∀ (a b c : ℤ) (hab : a < b) (hbc : b < c),
        x ⟨(a, b), hab⟩ + x ⟨(b, c), hbc⟩ ≤ x ⟨(a, c), by omega⟩)
    (B : ℝ)
    (hB : ∀ n : ℕ,
      (∫ x : BilateralArray, x ⟨(0, ((n + 1 : ℕ) : ℤ)), by omega⟩
        ∂(ρ : Measure BilateralArray)) / (n + 1 : ℝ) ≤ B)
    (q : ℝ)
    (hq : IsLUB (Set.range (fun n : ℕ =>
      (∫ x : BilateralArray, x ⟨(0, ((n + 1 : ℕ) : ℤ)), by omega⟩
        ∂(ρ : Measure BilateralArray)) / (n + 1 : ℝ))) q)
    (hforward : ∀ᵐ x ∂(ρ : Measure BilateralArray), Tendsto (fun n : ℕ =>
      x ⟨(0, (n + 1 : ℕ)), by omega⟩ / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 q)) :
    ∀ᵐ x ∂(ρ : Measure BilateralArray),
      limsup (fun n : ℕ => ((x ⟨(-((n + 1 : ℕ) : ℤ), (n + 1 : ℕ)), by omega⟩ /
        (2 * ((n + 1 : ℕ) : ℝ)) : ℝ) : EReal)) atTop ≤ (q : EReal) := by
  obtain ⟨q', _hq0, _hqB, hq', _hmean, ν, _r, _hr, _hweak, hfst, hT, hs, hm⟩ :=
    exists_bilateralJoint_stationary_majorant ρ hS hi hnonneg hadd B hB
  have heq : q' = q := hq'.unique hq
  subst q'
  exact ae_bilateralArray_centered_limsup_le_of_joint_majorant
    ρ ν ⟨measurable_fst, hfst⟩ hT (hm 0).1 q (hm 0).2.2
      (hs.mono fun _ hp => hp.2) hforward

end LPPDifferentiability
