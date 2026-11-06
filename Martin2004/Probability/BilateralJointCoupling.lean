/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.BilateralArrayRate
public import Martin2004.Probability.BilateralJointCompactness
public import Martin2004.Probability.BilateralJointLimitShift
public import Martin2004.Probability.BilateralJointLimitSupport

/-! One joint stationary additive majorant, with the actual expected rate
internally derived from the finite bound. This is a generic integrable-array
result; it does not discharge the hypotheses for a particular model. -/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace LPPDifferentiability

/-- A finite upper rate bound on an integrable stationary nonnegative
superadditive array yields one joint invariant law with the full original
marginal, simultaneous interval majorization and sharp coordinate moments.
The rate is the LUB of the actual positive origin expectations. -/
theorem exists_bilateralJoint_stationary_majorant
    (ρ : ProbabilityMeasure BilateralArray)
    (hS : MeasurePreserving bilateralArrayShift (ρ : Measure _) (ρ : Measure _))
    (hi : ∀ p : BilateralInterval, Integrable (fun x : BilateralArray => x p) (ρ : Measure _))
    (hnonneg : ∀ᵐ x ∂(ρ : Measure BilateralArray), ∀ p, 0 ≤ x p)
    (hadd : ∀ᵐ x ∂(ρ : Measure BilateralArray), ∀ (a b c : ℤ) (hab : a < b) (hbc : b < c),
      x ⟨(a, b), hab⟩ + x ⟨(b, c), hbc⟩ ≤ x ⟨(a, c), by omega⟩)
    (B : ℝ)
    (hB : ∀ n : ℕ,
      (∫ x : BilateralArray, x ⟨(0, ((n + 1 : ℕ) : ℤ)), by omega⟩ ∂(ρ : Measure _)) /
        (n + 1 : ℝ) ≤ B) :
    ∃ q : ℝ, 0 ≤ q ∧ q ≤ B ∧
      IsLUB (range (fun n : ℕ =>
        (∫ x : BilateralArray, x ⟨(0, ((n + 1 : ℕ) : ℤ)), by omega⟩ ∂(ρ : Measure _)) /
          (n + 1 : ℝ))) q ∧
      Tendsto (fun n : ℕ =>
        (∫ x : BilateralArray, x ⟨(0, ((n + 1 : ℕ) : ℤ)), by omega⟩ ∂(ρ : Measure _)) /
          (n + 1 : ℝ)) atTop (𝓝 q) ∧
      ∃ ν : ProbabilityMeasure BilateralJoint, ∃ r : ℕ → ℕ,
        StrictMono r ∧ Tendsto (uniformBilateralJointLaw ρ ∘ r) atTop (𝓝 ν) ∧
        (ν : Measure BilateralJoint).fst = (ρ : Measure BilateralArray) ∧
        MeasurePreserving bilateralJointShift (ν : Measure _) (ν : Measure _) ∧
        (∀ᵐ p ∂(ν : Measure BilateralJoint),
          (∀ t : ℤ, 0 ≤ p.2 t) ∧
          ∀ v : BilateralInterval, p.1 v ≤ ∑ t ∈ Finset.Ico v.1.1 v.1.2, p.2 t) ∧
        ∀ t : ℤ, Integrable (fun p : BilateralJoint => p.2 t) (ν : Measure _) ∧
          (∫ p : BilateralJoint, |p.2 t| ∂(ν : Measure _)) ≤ q ∧
          (∫ p : BilateralJoint, p.2 t ∂(ν : Measure _)) ≤ q := by
  obtain ⟨q, hq0, hqB, hqLUB, hq⟩ :=
    exists_bilateralArray_expected_rate ρ hS hi hnonneg hadd B hB
  obtain ⟨ν, r, hr, hweak, hfst, hmom⟩ :=
    exists_uniformBilateralJointLaw_tendsto_subseq ρ hS hi hnonneg hadd q hq
  refine ⟨q, hq0, hqB, hqLUB, hq, ν, r, hr, hweak, hfst, ?_, ?_, hmom⟩
  · exact measurePreserving_bilateralJointShift_of_tendsto_uniformBilateralJointLaw
      ρ hS ν r hr hweak
  · exact ae_weakLimit_uniformBilateralJointLaw_support ρ ν (hnonneg.and hadd) hr hweak

end LPPDifferentiability
