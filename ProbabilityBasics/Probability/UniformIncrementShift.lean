/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.UniformIncrementLaw
public import ProbabilityBasics.Probability.CesaroLaw
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Stationarity of the uniform-origin laws

This proves the stationarity claim that follows equation (2.13) of Liggett (1985).
It uses the product laws and positive indices, with no zeroth increment.
-/

public section

open MeasureTheory Filter Topology BoundedContinuousFunction

namespace LPPDifferentiability

/-- Shifting the increment sequence advances its positive origin by one. -/
theorem sequenceShift_originIncrementSequence {Ω : Type*} (X : ℕ → Ω → ℝ)
    (j : ℕ) (ω : Ω) :
    sequenceShift (originIncrementSequence X j ω) = originIncrementSequence X (j + 1) ω := by
  funext k
  change X (k + 1 + j + 2) ω - X (k + 1 + j + 1) ω =
    X (k + (j + 1) + 2) ω - X (k + (j + 1) + 1) ω
  rw [show k + 1 + j + 2 = k + (j + 1) + 2 by omega,
    show k + 1 + j + 1 = k + (j + 1) + 1 by omega]

/-- Summing a sequence shifted by one index leaves only its two end terms. -/
theorem sum_shift_sub (a : ℕ → ℝ) (m : ℕ) :
    (∑ u : Fin m, a (u.val + 1)) - (∑ u : Fin m, a u.val) = a m - a 0 := by
  induction m with
  | zero => simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_self]
  | succ m ih =>
    simp only [Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]
    linarith only [ih]

/-- Every interior term cancels in the finite-origin average. -/
theorem integral_uniformOriginIncrementLaw_shift_sub {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hm : ∀ j, 0 < j → Measurable (X j)) (n : ℕ)
    (f : (ℕ → ℝ) →ᵇ ℝ) :
    (∫ z, f (sequenceShift z) ∂(uniformOriginIncrementLaw μ X hm n : Measure (ℕ → ℝ))) -
      (∫ z, f z ∂(uniformOriginIncrementLaw μ X hm n : Measure (ℕ → ℝ))) =
      ((∫ ω, f (originIncrementSequence X (n + 1) ω) ∂μ) -
        (∫ ω, f (originIncrementSequence X 0 ω) ∂μ)) / (n + 1 : ℝ) := by
  let g := f.compContinuous ⟨sequenceShift, continuous_sequenceShift⟩
  change (∫ z, g z ∂_) - _ = _
  rw [integral_uniformOriginIncrementLaw, integral_uniformOriginIncrementLaw, ← sub_div]
  have hg (j : ℕ) :
      (∫ ω, g (originIncrementSequence X j ω) ∂μ) =
        ∫ ω, f (originIncrementSequence X (j + 1) ω) ∂μ := by
    congr 1
    funext ω
    exact congrArg f (sequenceShift_originIncrementSequence X j ω)
  simp_rw [hg]
  rw [sum_shift_sub (fun j => ∫ ω, f (originIncrementSequence X j ω) ∂μ) (n + 1)]

private theorem norm_integral_origin_test_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hm : ∀ j, 0 < j → Measurable (X j)) (j : ℕ)
    (f : (ℕ → ℝ) →ᵇ ℝ) :
    ‖∫ ω, f (originIncrementSequence X j ω) ∂μ‖ ≤ ‖f‖ := by
  rw [← integral_map (measurable_originIncrementSequence X hm j).aemeasurable
    f.continuous.measurable.aestronglyMeasurable]
  exact f.norm_integral_le_norm _

/-- The stationarity error of the law is controlled by two bounded endpoints. -/
theorem norm_integral_uniformOriginIncrementLaw_shift_sub_le {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hm : ∀ j, 0 < j → Measurable (X j)) (n : ℕ)
    (f : (ℕ → ℝ) →ᵇ ℝ) :
    ‖(∫ z, f (sequenceShift z) ∂(uniformOriginIncrementLaw μ X hm n : Measure (ℕ → ℝ))) -
      (∫ z, f z ∂(uniformOriginIncrementLaw μ X hm n : Measure (ℕ → ℝ)))‖ ≤
      2 * ‖f‖ / (n + 1 : ℝ) := by
  rw [integral_uniformOriginIncrementLaw_shift_sub, norm_div,
    Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ n + 1)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact (norm_sub_le _ _).trans (by
    linarith only [norm_integral_origin_test_le μ X hm (n + 1) f,
      norm_integral_origin_test_le μ X hm 0 f])

/-- A weak subsequential limit of the random-origin joint laws is stationary. -/
theorem measurePreserving_sequenceShift_of_tendsto_uniformOriginIncrementLaw
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hm : ∀ j, 0 < j → Measurable (X j))
    (ν : ProbabilityMeasure (ℕ → ℝ)) (r : ℕ → ℕ) (hr : StrictMono r)
    (hν : Tendsto (fun i => uniformOriginIncrementLaw μ X hm (r i)) atTop (𝓝 ν)) :
    MeasurePreserving sequenceShift (ν : Measure (ℕ → ℝ))
      (ν : Measure (ℕ → ℝ)) := by
  have hmapped := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun i => uniformOriginIncrementLaw μ X hm (r i)) ν hν continuous_sequenceShift
  refine ⟨measurable_sequenceShift, ?_⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  have hl := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hmapped f).sub
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hν f)
  have hz : Tendsto
      (fun i => (∫ z, f (sequenceShift z)
          ∂(uniformOriginIncrementLaw μ X hm (r i) : Measure (ℕ → ℝ))) -
        (∫ z, f z ∂(uniformOriginIncrementLaw μ X hm (r i) : Measure (ℕ → ℝ))))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun i =>
      norm_integral_uniformOriginIncrementLaw_shift_sub_le μ X hm (r i) f)
    have hd : Tendsto (fun n : ℕ => 2 * ‖f‖ / (n + 1 : ℝ)) atTop (𝓝 0) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (tendsto_add_atTop_iff_nat 1).2
          (tendsto_const_div_atTop_nhds_zero_nat (2 * ‖f‖))
    exact hd.comp hr.tendsto_atTop
  have hl' : Tendsto
      (fun i => (∫ z, f (sequenceShift z)
          ∂(uniformOriginIncrementLaw μ X hm (r i) : Measure (ℕ → ℝ))) -
        (∫ z, f z ∂(uniformOriginIncrementLaw μ X hm (r i) : Measure (ℕ → ℝ))))
      atTop (𝓝 ((∫ z, f z ∂((ν : Measure (ℕ → ℝ)).map sequenceShift)) -
        (∫ z, f z ∂(ν : Measure (ℕ → ℝ))))) := by
    convert hl using 1
    funext i
    rw [ProbabilityMeasure.toMeasure_map,
      integral_map measurable_sequenceShift.aemeasurable
        f.continuous.measurable.aestronglyMeasurable]
    simp only [ProbabilityMeasure.toMeasure_map]
  exact sub_eq_zero.mp (tendsto_nhds_unique hl' hz)

end LPPDifferentiability
