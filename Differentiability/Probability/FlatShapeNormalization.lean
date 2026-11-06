/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.UniformShapeTranslation
public import Martin2004.Probability.WeakNegativeShape
import Differentiability.Probability.NegativeMomentTranslation
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Tactic

/-! # Shape normalization under an actual upper bound

An almost-sure upper bound supplies the positive tail input needed by the
weak-negative shape theorem. Translating the actual marginal then gives the
same unique shape after adding the corresponding linear function.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace LPPDifferentiability

private theorem positive_integrated_sqrt_tail_lt_top_of_ae_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (M : ℝ)
    (hupper : ∀ᵐ x ∂μ, x ≤ M) :
    (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞ := by
  let R : ℝ := max M 0
  have hbad : μ {x : ℝ | M < x} = 0 := by
    simpa only [not_le] using (ae_iff.mp hupper)
  have hzero (t : ℝ) (ht : R < t) : μ (Ioi t) = 0 := by
    apply measure_mono_null (s := Ioi t) (t := {x : ℝ | M < x})
    · intro x hx
      simp only [mem_Ioi] at hx
      exact lt_of_le_of_lt (le_trans (le_max_left M 0) (le_of_lt ht)) hx
    · exact hbad
  have hdom : ∀ t ∈ Ioi (0 : ℝ),
      (μ (Ioi t)) ^ (1 / 2 : ℝ) ≤
        (Icc 0 R).indicator (fun _ : ℝ => (1 : ℝ≥0∞)) t := by
    intro t ht
    simp only [mem_Ioi] at ht
    by_cases htR : t ≤ R
    · have hmem : t ∈ Icc 0 R := ⟨le_of_lt ht, htR⟩
      rw [Set.indicator_of_mem hmem]
      have hμt : μ (Ioi t) ≤ 1 := by
        calc
          μ (Ioi t) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
          _ = 1 := measure_univ
      calc
        (μ (Ioi t)) ^ (1 / 2 : ℝ) ≤ (1 : ℝ≥0∞) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow hμt (by norm_num)
        _ = 1 := by rw [ENNReal.one_rpow]
    · have hgt : R < t := lt_of_not_ge htR
      have hnotmem : t ∉ Icc 0 R := by
        simp only [mem_Icc, not_and, not_le]
        exact fun _ => hgt
      rw [Set.indicator_of_notMem hnotmem, hzero t hgt]
      rw [ENNReal.zero_rpow_of_pos (by norm_num)]
  have hfinite :
      (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) ≤ ENNReal.ofReal R := by
    calc
      (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) ≤
          ∫⁻ t in Ioi (0 : ℝ), (Icc 0 R).indicator
            (fun _ : ℝ => (1 : ℝ≥0∞)) t :=
        setLIntegral_mono' measurableSet_Ioi hdom
      _ ≤ ∫⁻ t : ℝ, (Icc 0 R).indicator
            (fun _ : ℝ => (1 : ℝ≥0∞)) t ∂volume :=
        lintegral_mono' Measure.restrict_le_self le_rfl
      _ = volume (Icc 0 R) := by
        rw [lintegral_indicator_const measurableSet_Icc]
        simp
      _ = ENNReal.ofReal R := by
        rw [Real.volume_Icc]
        congr 1
        simp
  exact lt_of_le_of_lt hfinite ENNReal.ofReal_lt_top

/-- The actual translated marginal has the normalized upper bound and retains
the negative-part moment at its original exponent. -/
theorem translated_upper_bound_and_negative_moment
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (M p : ℝ)
    (hupper : ∀ᵐ x ∂μ, x ≤ M) (hp : 1 < p)
    (hmoment : (∫⁻ x, ENNReal.ofReal ((max (-x) 0) ^ p) ∂μ) < ∞) :
    (∀ᵐ y ∂(μ.map (fun x => x + (1 - M))), y ≤ 1) ∧
      (∫⁻ y, ENNReal.ofReal ((max (-y) 0) ^ p)
        ∂(μ.map (fun x => x + (1 - M)))) < ∞ := by
  have hupperShift :
      ∀ᵐ y ∂(μ.map (fun x => x + (1 - M))), y ≤ 1 := by
    apply (ae_map_iff
      (f := fun x : ℝ => x + (1 - M)) (μ := μ) (p := fun y => y ≤ 1)
      (by fun_prop) measurableSet_Iic).2
    filter_upwards [hupper] with x hx
    linarith
  have hmomentShift :=
    finite_lintegral_negativePart_rpow_map_add_of_lintegral_lt_top
      μ p (1 - M) hp hmoment
  exact ⟨hupperShift, hmomentShift⟩

/-- An actual almost-sure upper bound and one finite negative-part moment
determine the same unique shape before and after translation by `1 - M`. -/
theorem exists_unique_shape_with_upper_bound_normalization
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (M p : ℝ)
    (hupper : ∀ᵐ x ∂μ, x ≤ M) (hp : 1 < p)
    (hmoment : (∫⁻ x, ENNReal.ofReal ((max (-x) 0) ^ p) ∂μ) < ∞) :
    (∀ᵐ y ∂(μ.map (fun x => x + (1 - M))), y ≤ 1) ∧
    (∫⁻ y, ENNReal.ofReal ((max (-y) 0) ^ p)
      ∂(μ.map (fun x => x + (1 - M)))) < ∞ ∧
    ∃! g : Quadrant → ℝ,
      Continuous g ∧
      (∀ (a : ℝ≥0) (z : Quadrant),
        g (a * z.1, a * z.2) = (a : ℝ) * g z) ∧
      (∀ (x y : Quadrant) (a b : ℝ≥0), a + b = 1 →
        (a : ℝ) * g x + (b : ℝ) * g y ≤
          g (a * x.1 + b * y.1, a * x.2 + b * y.2)) ∧
      (∀ᵐ ω ∂environmentLaw μ, ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
          |lastPassage ω 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
            ε * ((d.1 + d.2 : ℕ) : ℝ)) ∧
      Continuous (fun z : Quadrant =>
        g z + (1 - M) * ((z.1 : ℝ) + (z.2 : ℝ))) ∧
      (∀ (a : ℝ≥0) (z : Quadrant),
        (g (a * z.1, a * z.2) +
          (1 - M) * ((a * z.1 : ℝ) + (a * z.2 : ℝ))) =
        (a : ℝ) * (g z + (1 - M) * ((z.1 : ℝ) + (z.2 : ℝ)))) ∧
      (∀ (x y : Quadrant) (a b : ℝ≥0), a + b = 1 →
        (a : ℝ) * (g x + (1 - M) * ((x.1 : ℝ) + (x.2 : ℝ))) +
          (b : ℝ) * (g y + (1 - M) * ((y.1 : ℝ) + (y.2 : ℝ))) ≤
        g (a * x.1 + b * y.1, a * x.2 + b * y.2) +
          (1 - M) * ((a * x.1 + b * y.1 : ℝ) + (a * x.2 + b * y.2 : ℝ))) ∧
      (∀ᵐ ω ∂environmentLaw (μ.map (fun x => x + (1 - M))),
        ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 1 ≤ N ∧
          ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
            |lastPassage ω 0 d -
              (g ((d.1 : ℝ≥0), (d.2 : ℝ≥0)) +
                (1 - M) * ((d.1 : ℝ) + (d.2 : ℝ)))| ≤
              ε * ((d.1 + d.2 : ℕ) : ℝ)) ∧
      (∀ h : Quadrant → ℝ,
        Continuous h →
        (∀ (a : ℝ≥0) (z : Quadrant),
          h (a * z.1, a * z.2) = (a : ℝ) * h z) →
        (∀ (x y : Quadrant) (a b : ℝ≥0), a + b = 1 →
          (a : ℝ) * h x + (b : ℝ) * h y ≤
            h (a * x.1 + b * y.1, a * x.2 + b * y.2)) →
        (∀ᵐ ω ∂environmentLaw (μ.map (fun x => x + (1 - M))),
          ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 1 ≤ N ∧
            ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
              |lastPassage ω 0 d - h ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
                ε * ((d.1 + d.2 : ℕ) : ℝ)) →
        h = fun z : Quadrant =>
          g z + (1 - M) * ((z.1 : ℝ) + (z.2 : ℝ))) := by
  obtain ⟨hupperShift, hmomentShift⟩ :=
    translated_upper_bound_and_negative_moment μ M p hupper hp hmoment
  have hpositive := positive_integrated_sqrt_tail_lt_top_of_ae_le μ M hupper
  have hpositiveShift :=
    positive_integrated_sqrt_tail_lt_top_of_ae_le
      (μ.map (fun x => x + (1 - M))) 1 hupperShift
  obtain ⟨g, hg, hUnique⟩ :=
    exists_unique_shape_of_negative_moment_and_positive_tail μ
      ⟨p, hp, hmoment⟩ hpositive
  obtain ⟨shiftedShape, _hshiftedShape, hUniqueShiftedShape⟩ :=
    exists_unique_shape_of_negative_moment_and_positive_tail
      (μ.map (fun x => x + (1 - M))) ⟨p, hp, hmomentShift⟩ hpositiveShift
  let c : ℝ := 1 - M
  let level : Quadrant → ℝ := fun z => (z.1 : ℝ) + (z.2 : ℝ)
  let shifted : Quadrant → ℝ := fun z => g z + c * level z
  have hlevelContinuous : Continuous level := by
    dsimp [level]
    fun_prop
  have hshiftedContinuous : Continuous shifted := by
    dsimp [shifted]
    exact hg.1.add (continuous_const.mul hlevelContinuous)
  have hshiftedHomogeneous : ∀ (a : ℝ≥0) (z : Quadrant),
      shifted (a * z.1, a * z.2) = (a : ℝ) * shifted z := by
    intro a z
    dsimp [shifted, level]
    rw [hg.2.1 a z]
    ring
  have hlevelMix (x y : Quadrant) (a b : ℝ≥0) :
      level (a * x.1 + b * y.1, a * x.2 + b * y.2) =
        (a : ℝ) * level x + (b : ℝ) * level y := by
    dsimp [level]
    ring
  have hshiftedConcave : ∀ (x y : Quadrant) (a b : ℝ≥0), a + b = 1 →
      (a : ℝ) * shifted x + (b : ℝ) * shifted y ≤
        shifted (a * x.1 + b * y.1, a * x.2 + b * y.2) := by
    intro x y a b hab
    dsimp [shifted]
    calc
      (a : ℝ) * (g x + c * level x) +
          (b : ℝ) * (g y + c * level y) =
        ((a : ℝ) * g x + (b : ℝ) * g y) +
          c * ((a : ℝ) * level x + (b : ℝ) * level y) := by ring
      _ ≤ g (a * x.1 + b * y.1, a * x.2 + b * y.2) +
          c * level (a * x.1 + b * y.1, a * x.2 + b * y.2) := by
        rw [← hlevelMix x y a b]
        calc
          _ = c * level (a * x.1 + b * y.1, a * x.2 + b * y.2) +
              ((a : ℝ) * g x + (b : ℝ) * g y) := by ring
          _ ≤ c * level (a * x.1 + b * y.1, a * x.2 + b * y.2) +
              g (a * x.1 + b * y.1, a * x.2 + b * y.2) :=
            by linarith [hg.2.2.1 x y a b hab]
          _ = g (a * x.1 + b * y.1, a * x.2 + b * y.2) +
              c * level (a * x.1 + b * y.1, a * x.2 + b * y.2) := by ring
  have hshiftedUniform : ∀ᵐ ω ∂environmentLaw (μ.map (fun x => x + c)),
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 1 ≤ N ∧
        ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
          |lastPassage ω 0 d -
            (g ((d.1 : ℝ≥0), (d.2 : ℝ≥0)) +
              c * ((d.1 : ℝ) + (d.2 : ℝ)))| ≤
            ε * ((d.1 + d.2 : ℕ) : ℝ) := by
    exact (uniform_origin_shape_law_iff_map_add μ g c).mp hg.2.2.2
  have hshiftedUnique : ∀ h : Quadrant → ℝ,
      Continuous h →
      (∀ (a : ℝ≥0) (z : Quadrant),
        h (a * z.1, a * z.2) = (a : ℝ) * h z) →
      (∀ (x y : Quadrant) (a b : ℝ≥0), a + b = 1 →
        (a : ℝ) * h x + (b : ℝ) * h y ≤
          h (a * x.1 + b * y.1, a * x.2 + b * y.2)) →
      (∀ᵐ ω ∂environmentLaw (μ.map (fun x => x + c)),
        ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 1 ≤ N ∧
          ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
            |lastPassage ω 0 d - h ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
              ε * ((d.1 + d.2 : ℕ) : ℝ)) → h = shifted := by
    intro h hhContinuous hhHomogeneous hhConcave hhUniform
    have hEq := hUniqueShiftedShape h
      ⟨hhContinuous, hhHomogeneous, hhConcave, hhUniform⟩
    have hShiftEq := hUniqueShiftedShape shifted
      ⟨hshiftedContinuous, hshiftedHomogeneous, hshiftedConcave, hshiftedUniform⟩
    exact hEq.trans hShiftEq.symm
  have hShapeFormula : shifted = fun z : Quadrant =>
      g z + (1 - M) * ((z.1 : ℝ) + (z.2 : ℝ)) := by
    funext z
    rfl
  refine ⟨hupperShift, hmomentShift, g, ?_, ?_⟩
  · simpa only [c, hShapeFormula] using
      ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2,
        hshiftedContinuous, hshiftedHomogeneous, hshiftedConcave,
        hshiftedUniform, hshiftedUnique⟩
  · intro f hf
    exact hUnique f ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1⟩

end LPPDifferentiability
