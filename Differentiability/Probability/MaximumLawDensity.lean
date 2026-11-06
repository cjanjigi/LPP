/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The density of the maximum of two independent samples

The strict/nonstrict split preserves atoms: ties are assigned to the first
sample. This is the one-site density calculation in part (i) of Lemma 4.1 of
the differentiability preprint. No moment or support assumption is used.

## References

C. Janjigian, F. Rassoul-Agha and T. Seppäläinen, *Differentiability of the shape
function in the planar corner growth model*, preprint.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace LPPDifferentiability

private theorem measurable_measure_Iic (μ : Measure ℝ) :
    Measurable (fun t : ℝ => μ (Iic t)) :=
  (show Monotone (fun t : ℝ => μ (Iic t)) from
    fun _ _ h => measure_mono (Iic_subset_Iic.mpr h)).measurable

private theorem measurable_measure_Iio (μ : Measure ℝ) :
    Measurable (fun t : ℝ => μ (Iio t)) :=
  (show Monotone (fun t : ℝ => μ (Iio t)) from
    fun _ _ h => measure_mono (Iio_subset_Iio h)).measurable

/-- The maximum of two independent samples has density `F(t) + F(t-)`.
The strict second tail accounts for ties, including laws with atoms. -/
theorem map_max_eq_withDensity (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (μ.prod μ).map (fun p : ℝ × ℝ => max p.1 p.2) =
      μ.withDensity (fun t => μ (Iic t) + μ (Iio t)) := by
  classical
  ext B hB
  let A : Set (ℝ × ℝ) := {p | p.1 ∈ B ∧ p.2 ≤ p.1}
  let C : Set (ℝ × ℝ) := {p | p.2 ∈ B ∧ p.1 < p.2}
  have hA : MeasurableSet A :=
    (hB.preimage measurable_fst).inter (measurableSet_le measurable_snd measurable_fst)
  have hC : MeasurableSet C :=
    (hB.preimage measurable_snd).inter (measurableSet_lt measurable_fst measurable_snd)
  have hdisj : Disjoint A C := by
    rw [Set.disjoint_left]
    intro p hpA hpC
    exact (not_lt_of_ge hpA.2) hpC.2
  have hsplit : (fun p : ℝ × ℝ => max p.1 p.2) ⁻¹' B = A ∪ C := by
    ext p
    by_cases h : p.2 ≤ p.1
    · simp only [mem_preimage, max_eq_left h, mem_union, A, C, mem_ofPred_eq]
      exact ⟨fun hp => Or.inl ⟨hp, h⟩, fun hp => hp.elim And.left
        (fun hc => False.elim ((not_lt_of_ge h) hc.2))⟩
    · have hlt : p.1 < p.2 := lt_of_not_ge h
      simp only [mem_preimage, max_eq_right hlt.le, mem_union, A, C, mem_ofPred_eq]
      exact ⟨fun hp => Or.inr ⟨hp, hlt⟩, fun hp => hp.elim
        (fun ha => False.elim (h ha.2)) And.left⟩
  have hfirst : (μ.prod μ) A = ∫⁻ t in B, μ (Iic t) ∂μ := by
    rw [Measure.prod_apply hA, ← lintegral_indicator hB]
    apply lintegral_congr
    intro t
    by_cases ht : t ∈ B
    · simp only [A, Set.preimage_ofPred_eq, ht, true_and, Set.indicator_of_mem ht]
      rfl
    · simp [A, ht]
  have hsecond : (μ.prod μ) C = ∫⁻ t in B, μ (Iio t) ∂μ := by
    rw [Measure.prod_apply_symm hC, ← lintegral_indicator hB]
    apply lintegral_congr
    intro t
    by_cases ht : t ∈ B
    · simp only [C, Set.preimage_ofPred_eq, ht, true_and, Set.indicator_of_mem ht]
      rfl
    · simp [C, ht]
  rw [Measure.map_apply (measurable_fst.max measurable_snd) hB, hsplit,
    measure_union hdisj hC, hfirst, hsecond, withDensity_apply _ hB,
    lintegral_add_left (measurable_measure_Iic μ)]

/-- The real density of the maximum is nonnegative and bounded by two. -/
theorem maximum_density_mem_Icc (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    μ.real (Iic t) + μ.real (Iio t) ∈ Icc (0 : ℝ) 2 := by
  constructor
  · exact add_nonneg measureReal_nonneg measureReal_nonneg
  · have h₁ : μ.real (Iic t) ≤ 1 := measureReal_le_one
    have h₂ : μ.real (Iio t) ≤ 1 := measureReal_le_one
    linarith only [h₁, h₂]

/-- The real maximum density is measurable. -/
theorem measurable_maximum_density (μ : Measure ℝ) :
    Measurable (fun t => μ.real (Iic t) + μ.real (Iio t)) :=
  (measurable_measure_Iic μ).ennreal_toReal.add
    (measurable_measure_Iio μ).ennreal_toReal

/-- The actual maximum density has a finite first moment under its base law. -/
theorem integrable_maximum_density (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Integrable (fun t => μ.real (Iic t) + μ.real (Iio t)) μ :=
  Integrable.of_mem_Icc 0 2 (measurable_maximum_density μ).aemeasurable
    (Filter.Eventually.of_forall (maximum_density_mem_Icc μ))

/-- The real maximum density has mean one, by the total mass of the maximum law. -/
theorem integral_maximum_density (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (∫ t, μ.real (Iic t) + μ.real (Iio t) ∂μ) = 1 := by
  have hmass : (∫⁻ t, μ (Iic t) + μ (Iio t) ∂μ) = 1 := by
    have heq := congrArg (fun ν : Measure ℝ => ν univ) (map_max_eq_withDensity μ)
    simpa only [Measure.map_apply (measurable_fst.max measurable_snd) MeasurableSet.univ,
      preimage_univ, measure_univ, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ] using heq.symm
  have hfinite : ∀ᵐ t ∂μ, μ (Iic t) + μ (Iio t) < ∞ :=
    Filter.Eventually.of_forall (fun t => ENNReal.add_lt_top.mpr
      ⟨measure_lt_top μ (Iic t), measure_lt_top μ (Iio t)⟩)
  calc
    (∫ t, μ.real (Iic t) + μ.real (Iio t) ∂μ) =
        ∫ t, (μ (Iic t) + μ (Iio t)).toReal ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t =>
        (ENNReal.toReal_add (measure_ne_top μ (Iic t)) (measure_ne_top μ (Iio t))).symm
    _ = (∫⁻ t, μ (Iic t) + μ (Iio t) ∂μ).toReal :=
      integral_toReal ((measurable_measure_Iic μ).add
        (measurable_measure_Iio μ)).aemeasurable hfinite
    _ = 1 := by rw [hmass]; rfl

/-- The square of the maximum density is integrable, without moments of `μ`. -/
theorem integrable_maximum_density_sq (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Integrable (fun t => (μ.real (Iic t) + μ.real (Iio t)) ^ 2) μ := by
  apply Integrable.of_mem_Icc 0 4 (measurable_maximum_density μ |>.pow_const 2).aemeasurable
  exact Filter.Eventually.of_forall fun t => by
    have ht := maximum_density_mem_Icc μ t
    constructor
    · exact sq_nonneg _
    · nlinarith only [mul_self_le_mul_self ht.1 ht.2]

/-- A probability mixture with maximum resampling has integrable density. -/
theorem integrable_maximum_mixture_density (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (δ : ℝ) :
    Integrable (fun t => 1 - δ + δ * (μ.real (Iic t) + μ.real (Iio t))) μ :=
  (integrable_const (1 - δ)).add ((integrable_maximum_density μ).const_mul δ)

/-- The squared one-site mixture density is integrable for `0 ≤ δ ≤ 1`. -/
theorem integrable_maximum_mixture_density_sq (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {δ : ℝ} (hδ : δ ∈ Icc (0 : ℝ) 1) :
    Integrable (fun t => (1 - δ + δ * (μ.real (Iic t) + μ.real (Iio t))) ^ 2) μ := by
  have hg : Measurable (fun t => 1 - δ + δ * (μ.real (Iic t) + μ.real (Iio t))) :=
    measurable_const.add (measurable_const.mul (measurable_maximum_density μ))
  apply Integrable.of_mem_Icc 0 4 (hg.pow_const 2).aemeasurable
  exact Filter.Eventually.of_forall fun t => by
    have ht := maximum_density_mem_Icc μ t
    have hg0 : 0 ≤ 1 - δ + δ * (μ.real (Iic t) + μ.real (Iio t)) := by
      nlinarith only [hδ.2, mul_nonneg hδ.1 ht.1]
    have hg2 : 1 - δ + δ * (μ.real (Iic t) + μ.real (Iio t)) ≤ 2 := by
      nlinarith only [hδ.2, mul_nonneg hδ.1 (sub_nonneg.mpr ht.2)]
    exact ⟨sq_nonneg _, by nlinarith only [mul_self_le_mul_self hg0 hg2]⟩

/-- The exact one-site squared-density estimate, including endpoints. -/
theorem integral_maximum_mixture_density_sq_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {δ : ℝ} (hδ : δ ∈ Icc (0 : ℝ) 1) :
    (∫ t, (1 - δ + δ * (μ.real (Iic t) + μ.real (Iio t))) ^ 2 ∂μ) ≤
      Real.exp (3 * δ ^ 2) := by
  let h : ℝ → ℝ := fun t => μ.real (Iic t) + μ.real (Iio t)
  have hi : Integrable h μ := integrable_maximum_density μ
  have hgi := integrable_maximum_mixture_density_sq μ hδ
  have hbound : Integrable
      (fun t => (1 - δ) ^ 2 + (2 * δ * (1 - δ)) * h t + 4 * δ ^ 2) μ :=
    ((integrable_const _).add (hi.const_mul _)).add (integrable_const _)
  calc
    (∫ t, (1 - δ + δ * h t) ^ 2 ∂μ) ≤
        ∫ t, (1 - δ) ^ 2 + (2 * δ * (1 - δ)) * h t + 4 * δ ^ 2 ∂μ := by
      apply integral_mono hgi hbound
      intro t
      have ht := maximum_density_mem_Icc μ t
      have hs : h t ^ 2 ≤ 4 := by
        change (μ.real (Iic t) + μ.real (Iio t)) ^ 2 ≤ 4
        nlinarith only [mul_self_le_mul_self ht.1 ht.2]
      nlinarith only [mul_le_mul_of_nonneg_left hs (sq_nonneg δ)]
    _ = 1 + 3 * δ ^ 2 := by
      have hlinear : Integrable
          (fun t => (1 - δ) ^ 2 + (2 * δ * (1 - δ)) * h t) μ :=
        (integrable_const ((1 - δ) ^ 2)).add (hi.const_mul (2 * δ * (1 - δ)))
      rw [integral_add hlinear (integrable_const (4 * δ ^ 2)),
        integral_add (integrable_const ((1 - δ) ^ 2))
          (hi.const_mul (2 * δ * (1 - δ))), integral_const_mul]
      simp only [integral_const, probReal_univ, one_smul,
        show (∫ t, h t ∂μ) = 1 from integral_maximum_density μ, mul_one]
      ring
    _ ≤ Real.exp (3 * δ ^ 2) := by
      simpa only [add_comm] using Real.add_one_le_exp (3 * δ ^ 2)

end LPPDifferentiability
