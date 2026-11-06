/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.BilateralJointLaw
public import Martin2004.Probability.BilateralIncrementMoments
public import ProbabilityBasics.Probability.JointProductTightness
public import ProbabilityBasics.Probability.WeakMeanLimit

/-!
# A single joint weak limit of the actual bilateral laws

Coordinate integrals below are literal pushforward identities for the existing
finite uniform-root sampler. The compactness construction retains the entire
array marginal and uses the same weak limit at every integer coordinate.
-/

public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace LPPDifferentiability

/-- Unbounded measurable coordinate tests use the actual uniform-root sampler. -/
theorem integral_uniformBilateralJointLaw_coordinate
    (ρ : ProbabilityMeasure BilateralArray) (N : ℕ) (t : ℤ)
    (g : ℝ → ℝ) (hg : Measurable g) :
    (∫ p : BilateralJoint, g (p.2 t) ∂(uniformBilateralJointLaw ρ N : Measure _)) =
      ∫ p : BilateralArray × Fin (N + 1),
        g (bilateralArrayIncrements p.2.val p.1 t)
          ∂uniformOriginProduct (ρ : Measure _) N := by
  rw [uniformBilateralJointLaw_toMeasure]
  exact integral_map (measurable_uniformBilateralJointSampler N).aemeasurable
    (hg.comp ((measurable_pi_apply t).comp measurable_snd)).aestronglyMeasurable

/-- Genuine coordinate integrability is equivalent to integrability under the
literal sampler; no bounded-test restriction is used. -/
theorem integrable_uniformBilateralJointLaw_coordinate_iff
    (ρ : ProbabilityMeasure BilateralArray) (N : ℕ) (t : ℤ)
    (g : ℝ → ℝ) (hg : Measurable g) :
    Integrable (fun p : BilateralJoint => g (p.2 t))
        (uniformBilateralJointLaw ρ N : Measure _) ↔
      Integrable (fun p : BilateralArray × Fin (N + 1) =>
        g (bilateralArrayIncrements p.2.val p.1 t))
          (uniformOriginProduct (ρ : Measure _) N) := by
  rw [uniformBilateralJointLaw_toMeasure]
  exact integrable_map_measure
    (hg.comp ((measurable_pi_apply t).comp measurable_snd)).aestronglyMeasurable
    (measurable_uniformBilateralJointSampler N).aemeasurable

private theorem integrable_coordinate_of_weak_abs_integral_tendsto_le
    (ν : ℕ → ProbabilityMeasure BilateralJoint) (κ : ProbabilityMeasure BilateralJoint)
    (hweak : Tendsto ν atTop (𝓝 κ)) (t : ℤ)
    (hi : ∀ n, Integrable (fun p : BilateralJoint => p.2 t) (ν n : Measure _))
    (q : ℝ)
    (hmean : Tendsto (fun n => ∫ p : BilateralJoint, |p.2 t| ∂(ν n : Measure _))
      atTop (𝓝 q)) :
    Integrable (fun p : BilateralJoint => p.2 t) (κ : Measure _) ∧
      (∫ p : BilateralJoint, |p.2 t| ∂(κ : Measure _)) ≤ q ∧
      (∫ p : BilateralJoint, p.2 t ∂(κ : Measure _)) ≤ q := by
  let f : BilateralJoint → ℝ := fun p => p.2 t
  have hf : Measurable f := (measurable_pi_apply t).comp measurable_snd
  let μ : ℕ → ProbabilityMeasure ℝ := fun n => (ν n).map f
  let κt : ProbabilityMeasure ℝ := κ.map f
  have hμweak : Tendsto μ atTop (𝓝 κt) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous ν κ hweak
      ((continuous_apply t).comp continuous_snd)
  have hμi (n : ℕ) : Integrable (fun y : ℝ => |y|) (μ n : Measure ℝ) := by
    change Integrable (fun y : ℝ => |y|) ((ν n : Measure _).map f)
    exact (integrable_map_measure continuous_abs.measurable.aestronglyMeasurable hf.aemeasurable).2
      (hi n).abs
  have hμint (n : ℕ) :
      (∫ y : ℝ, |y| ∂(μ n : Measure ℝ)) =
        ∫ p : BilateralJoint, |p.2 t| ∂(ν n : Measure _) :=
    integral_map hf.aemeasurable continuous_abs.measurable.aestronglyMeasurable
  have hμmean : Tendsto (fun n => ∫ y : ℝ, |y| ∂(μ n : Measure ℝ))
      atTop (𝓝 q) := hmean.congr fun n => (hμint n).symm
  obtain ⟨hκi, hκbound⟩ := integrable_nonneg_of_weak_integral_tendsto_le
    μ κt hμweak (fun y : ℝ => |y|) continuous_abs abs_nonneg hμi q hμmean
  have hiabs : Integrable (fun p : BilateralJoint => |p.2 t|) (κ : Measure _) :=
    (integrable_map_measure continuous_abs.measurable.aestronglyMeasurable hf.aemeasurable).1 hκi
  have hiκ : Integrable (fun p : BilateralJoint => p.2 t) (κ : Measure _) :=
    (integrable_norm_iff hf.aestronglyMeasurable).1 hiabs
  have hbound : (∫ p : BilateralJoint, |p.2 t| ∂(κ : Measure _)) ≤ q := by
    have he : (∫ y : ℝ, |y| ∂(κt : Measure ℝ)) =
        ∫ p : BilateralJoint, |p.2 t| ∂(κ : Measure _) :=
      integral_map hf.aemeasurable continuous_abs.measurable.aestronglyMeasurable
    exact he ▸ hκbound
  exact ⟨hiκ, hbound, (le_abs_self _).trans (abs_integral_le_integral_abs.trans hbound)⟩

/-- One subsequential weak limit of the actual finite joint laws retains the
whole array law and has sharp first absolute moments at every integer
coordinate. Tightness and all moment estimates are proved from the displayed
assumptions. All coordinate conclusions hold for this same witness. -/
theorem exists_uniformBilateralJointLaw_tendsto_subseq
    (ρ : ProbabilityMeasure BilateralArray)
    (hS : MeasurePreserving bilateralArrayShift (ρ : Measure _) (ρ : Measure _))
    (hi : ∀ p : BilateralInterval, Integrable (fun x : BilateralArray => x p) (ρ : Measure _))
    (hnonneg : ∀ᵐ x ∂(ρ : Measure BilateralArray), ∀ p, 0 ≤ x p)
    (hadd : ∀ᵐ x ∂(ρ : Measure BilateralArray), ∀ (a b c : ℤ) (hab : a < b) (hbc : b < c),
      x ⟨(a, b), hab⟩ + x ⟨(b, c), hbc⟩ ≤ x ⟨(a, c), by omega⟩)
    (q : ℝ)
    (ha : Tendsto (fun n : ℕ =>
      (∫ x : BilateralArray, x ⟨(0, (((n) + 1 : ℕ) : ℤ)), by omega⟩ ∂(ρ : Measure _)) /
        (n + 1 : ℝ)) atTop (𝓝 q)) :
    ∃ ν : ProbabilityMeasure BilateralJoint, ∃ r : ℕ → ℕ,
      StrictMono r ∧ Tendsto (uniformBilateralJointLaw ρ ∘ r) atTop (𝓝 ν) ∧
      (ν : Measure BilateralJoint).fst = (ρ : Measure BilateralArray) ∧
      ∀ t : ℤ, Integrable (fun p : BilateralJoint => p.2 t) (ν : Measure _) ∧
        (∫ p : BilateralJoint, |p.2 t| ∂(ν : Measure _)) ≤ q ∧
        (∫ p : BilateralJoint, p.2 t ∂(ν : Measure _)) ≤ q := by
  classical
  have hiLaw (N : ℕ) (t : ℤ) :
      Integrable (fun p : BilateralJoint => p.2 t)
        (uniformBilateralJointLaw ρ N : Measure _) :=
    (integrable_uniformBilateralJointLaw_coordinate_iff ρ N t id measurable_id).2
      (integrable_uniform_bilateralArrayIncrements ρ hi N t)
  have hC : ∀ t : ℤ, ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      (∫ p : BilateralArray × Fin (N + 1), |bilateralArrayIncrements p.2.val p.1 t|
        ∂uniformOriginProduct (ρ : Measure _) N) ≤ C :=
    exists_uniform_abs_integral_bilateralArrayIncrements_le ρ hS hi hnonneg hadd q ha
  choose C hC0 hCbound using hC
  have hlin (N : ℕ) (t : ℤ) :
      (∫⁻ p : BilateralJoint, ENNReal.ofReal ‖p.2 t‖
        ∂(uniformBilateralJointLaw ρ N : Measure _)) ≤ ENNReal.ofReal (C t) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hiLaw N t).norm
      (ae_of_all _ fun p => norm_nonneg (p.2 t))]
    apply ENNReal.ofReal_le_ofReal
    rw [show (fun p : BilateralJoint => ‖p.2 t‖) = (fun p => |p.2 t|) from rfl,
      integral_uniformBilateralJointLaw_coordinate ρ N t abs continuous_abs.measurable]
    exact hCbound t N
  obtain ⟨ν, r, hr, hweak, hfst⟩ :=
    exists_joint_probabilityMeasure_tendsto_subseq_of_coordinate_moments ρ
      (uniformBilateralJointLaw ρ)
      (fun N => (uniformBilateralJointLaw_fst ρ N).map_eq)
      (fun t => ENNReal.ofReal (C t)) (fun _ => ENNReal.ofReal_ne_top) hlin
  refine ⟨ν, r, hr, hweak, hfst, fun t => ?_⟩
  apply integrable_coordinate_of_weak_abs_integral_tendsto_le
    (uniformBilateralJointLaw ρ ∘ r) ν hweak t (fun n => hiLaw (r n) t) q
  have hmean := (tendsto_integral_uniform_bilateralArrayIncrements ρ hS hi q ha t).comp
    hr.tendsto_atTop
  apply hmean.congr
  intro n
  change (∫ p : BilateralArray × Fin (r n + 1), bilateralArrayIncrements p.2.val p.1 t
    ∂uniformOriginProduct (ρ : Measure _) (r n)) = _
  change _ = ∫ p : BilateralJoint, |p.2 t| ∂(uniformBilateralJointLaw ρ (r n) : Measure _)
  rw [integral_uniformBilateralJointLaw_coordinate ρ (r n) t abs continuous_abs.measurable]
  apply integral_congr_ae
  filter_upwards [ae_nonneg_uniform_bilateralArrayIncrements ρ hnonneg hadd (r n) t]
    with p hp
  exact (abs_of_nonneg hp).symm

end LPPDifferentiability
