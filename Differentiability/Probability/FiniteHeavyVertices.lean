/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Probability.CoordinateLaw
public import ProbabilityBasics.Probability.PositiveMomentTail
public import Mathlib.Data.Finset.Basic
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Finite upper-heavy-site bounds

For a fixed finite set of sites, a positive moment bounds the probability that some site is
strictly above a threshold. The complement gives a bound for the probability that all sites are at
or below the threshold.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace LPPDifferentiability

/-- The probability that some site of a finite set is strictly above a threshold `t` is at most
its cardinality times the positive-part moment and the factor `t ^ (-p)`. The same bound gives a
lower bound for the probability that every site is at or below `t`. -/
theorem measureReal_exists_upper_heavy_site_le_and_safe_ge
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {p : ℝ} (hp : 0 < p)
    (hmoment : (∫⁻ x, ENNReal.ofReal ((max x 0) ^ p) ∂μ) < ∞)
    (t : ℝ) (ht : 0 < t) (S : Finset Lattice) :
    MeasurableSet {ω : Environment | ∃ z ∈ S, t < ω z} ∧
      (environmentLaw μ).real {ω : Environment | ∃ z ∈ S, t < ω z} ≤
        (S.card : ℝ) * (∫ x : ℝ, (max x 0) ^ p ∂μ) * t ^ (-p) ∧
      (MeasurableSet {ω : Environment | ∀ z ∈ S, ω z ≤ t} ∧
        (environmentLaw μ).real {ω : Environment | ∀ z ∈ S, ω z ≤ t} ≥
          max 0 (1 - (S.card : ℝ) * (∫ x : ℝ, (max x 0) ^ p ∂μ) * t ^ (-p))) := by
  classical
  let moment : ℝ := ∫ x : ℝ, (max x 0) ^ p ∂μ
  let bad : Lattice → Set Environment := fun z => {ω | t < ω z}
  have hEvent :
      {ω : Environment | ∃ z ∈ S, t < ω z} = ⋃ z ∈ S, bad z := by
    ext ω
    simp [bad]
  have hBadMeas : MeasurableSet {ω : Environment | ∃ z ∈ S, t < ω z} := by
    rw [hEvent]
    exact Finset.measurableSet_biUnion S fun z _ =>
      measurableSet_lt measurable_const (measurable_environment_eval z)
  have hTail : μ.real (Ioi t) ≤ moment * t ^ (-p) := by
    calc
      μ.real (Ioi t) ≤ moment / t ^ p :=
        positive_tail_le_moment_div_rpow μ hp hmoment ht
      _ = moment * t ^ (-p) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg ht.le]
  have hMarginal (z : Lattice) :
      (environmentLaw μ).real (bad z) = μ.real (Ioi t) := by
    have hSet : bad z = (fun ω : Environment => ω z) ⁻¹' Ioi t := by
      ext ω
      simp [bad]
    rw [hSet]
    change ((environmentLaw μ) ((fun ω : Environment => ω z) ⁻¹' Ioi t)).toReal =
      (μ (Ioi t)).toReal
    calc
      ((environmentLaw μ) ((fun ω : Environment => ω z) ⁻¹' Ioi t)).toReal =
          (((environmentLaw μ).map (fun ω : Environment => ω z)) (Ioi t)).toReal := by
        rw [Measure.map_apply (measurable_environment_eval z) measurableSet_Ioi]
      _ = (μ (Ioi t)).toReal := by rw [environmentLaw_map_eval μ z]
  have hEach (z : Lattice) :
      (environmentLaw μ).real (bad z) ≤ moment * t ^ (-p) := by
    rw [hMarginal z]
    exact hTail
  have hBadBound :
      (environmentLaw μ).real {ω : Environment | ∃ z ∈ S, t < ω z} ≤
        (S.card : ℝ) * moment * t ^ (-p) := by
    rw [hEvent]
    calc
      (environmentLaw μ).real (⋃ z ∈ S, bad z) ≤
          ∑ z ∈ S, (environmentLaw μ).real (bad z) :=
        measureReal_biUnion_finset_le S bad
      _ ≤ ∑ z ∈ S, moment * t ^ (-p) :=
        Finset.sum_le_sum fun z _ => hEach z
      _ = (S.card : ℝ) * moment * t ^ (-p) := by simp [mul_assoc]
  have hSafeEq :
      {ω : Environment | ∀ z ∈ S, ω z ≤ t} =
        ({ω : Environment | ∃ z ∈ S, t < ω z})ᶜ := by
    ext ω
    simp [not_lt]
  have hSafeMeas : MeasurableSet {ω : Environment | ∀ z ∈ S, ω z ≤ t} := by
    rw [hSafeEq]
    exact hBadMeas.compl
  have hSafeNonneg :
      0 ≤ (environmentLaw μ).real {ω : Environment | ∀ z ∈ S, ω z ≤ t} :=
    measureReal_nonneg
  have hSafeTail :
      1 - (S.card : ℝ) * moment * t ^ (-p) ≤
        (environmentLaw μ).real {ω : Environment | ∀ z ∈ S, ω z ≤ t} := by
    rw [hSafeEq, probReal_compl_eq_one_sub (μ := environmentLaw μ) hBadMeas]
    linarith only [hBadBound]
  have hSafeBound :
      max 0 (1 - (S.card : ℝ) * moment * t ^ (-p)) ≤
        (environmentLaw μ).real {ω : Environment | ∀ z ∈ S, ω z ≤ t} :=
    max_le_iff.mpr ⟨hSafeNonneg, hSafeTail⟩
  refine ⟨hBadMeas, ?_, hSafeMeas, ?_⟩
  · simpa only [moment] using hBadBound
  · simpa only [moment] using hSafeBound

end LPPDifferentiability

end
