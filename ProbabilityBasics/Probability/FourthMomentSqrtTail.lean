/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.PositiveMomentTail
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-!
# Integrated square-root tail from a fourth moment

If a probability measure on the real line has a finite fourth moment of its positive part, then
the integral over `t > 0` of the square root of its tail `P(X > t)` is bounded by twice the
fourth root of that moment. The proof splits the integral at the fourth root of the moment and
uses Markov's inequality on the part above it.
-/

public section
open MeasureTheory Set Filter
open scoped ENNReal

namespace LPPDifferentiability

/-- A finite fourth positive moment gives the integrated square-root tail bound, including the case
where that moment is zero. -/
theorem integrated_sqrt_positive_tail_le_two_fourth_root
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hfourth : (∫⁻ x, ENNReal.ofReal ((max x 0)^4) ∂ν) < ∞) :
    (∫⁻ t in Ioi (0 : ℝ), (ν (Ioi t))^(1/2 : ℝ)) ≤
      ENNReal.ofReal (2 * (∫ x : ℝ, (max x 0)^4 ∂ν)^(1/4 : ℝ)) := by
  let M : ℝ := ∫ x : ℝ, (max x 0)^(4 : ℝ) ∂ν
  let a : ℝ := M^(4⁻¹ : ℝ)
  let f : ℝ → ℝ := fun t => (ν.real (Ioi t))^(1/2 : ℝ)
  have hM0 : 0 ≤ M := by
    dsimp [M]
    exact integral_nonneg fun x => Real.rpow_nonneg (le_max_right x 0) _
  have hMnat : M = ∫ x : ℝ, (max x 0)^4 ∂ν := by
    dsimp [M]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x : ℝ =>
      Real.rpow_natCast (max x 0) 4)
  have haTarget : a = (∫ x : ℝ, (max x 0)^4 ∂ν)^(1/4 : ℝ) := by
    dsimp [a]
    rw [← hMnat]
    congr 1
    norm_num
  have ha0 : 0 ≤ a := Real.rpow_nonneg hM0 _
  have htailAnti : Antitone (fun t : ℝ => ν.real (Ioi t)) := by
    intro x y hxy
    exact measureReal_mono (Ioi_subset_Ioi hxy)
  have hfMeas : Measurable f :=
    (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 2)).measurable.comp
      htailAnti.measurable
  have hf0 (t : ℝ) : 0 ≤ f t := Real.rpow_nonneg measureReal_nonneg _
  have hfLeOne (t : ℝ) : f t ≤ 1 := by
    dsimp [f]
    simpa only [Real.one_rpow] using
      (Real.rpow_le_rpow measureReal_nonneg measureReal_le_one
        (by norm_num : (0 : ℝ) ≤ 1 / 2))
  have htailENN (t : ℝ) : (ν (Ioi t))^(1/2 : ℝ) = ENNReal.ofReal (f t) := by
    dsimp [f]
    rw [measureReal_def,
      ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg
        (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ENNReal.ofReal_toReal (measure_ne_top ν (Ioi t))]
  have hmarkov (t : ℝ) (ht : 0 < t) : ν.real (Ioi t) ≤ M / t^(4 : ℝ) := by
    have hfourthRpow :
        (∫⁻ x, ENNReal.ofReal ((max x 0)^(4 : ℝ)) ∂ν) < ∞ := by
      have heq :
          (∫⁻ x, ENNReal.ofReal ((max x 0)^(4 : ℝ)) ∂ν) =
            ∫⁻ x, ENNReal.ofReal ((max x 0)^4) ∂ν := by
        exact lintegral_congr fun x =>
          congrArg ENNReal.ofReal (Real.rpow_natCast (max x 0) 4)
      rw [heq]
      exact hfourth
    have h := positive_tail_le_moment_div_rpow ν (p := (4 : ℝ))
      (by norm_num : (0 : ℝ) < 4) hfourthRpow ht
    simpa only [M] using h
  by_cases ha : a = 0
  · have hMzero : M = 0 := by
      by_contra hMne
      have hMpos : 0 < M := lt_of_le_of_ne hM0 (Ne.symm hMne)
      have hapos : 0 < a := Real.rpow_pos_of_pos hMpos _
      exact (ne_of_gt hapos) ha
    have htailzero (t : ℝ) (ht : 0 < t) : ν.real (Ioi t) = 0 := by
      have hm := hmarkov t ht
      refine le_antisymm ?_ measureReal_nonneg
      simpa [hMzero] using hm
    have hzeroAE : (fun t : ℝ => (ν (Ioi t))^(1/2 : ℝ)) =ᵐ[volume.restrict (Ioi 0)] 0 := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [htailENN t]
      simp [f, htailzero t ht]
    calc
      _ = ∫⁻ t, (0 : ℝ≥0∞) ∂volume.restrict (Ioi 0) := lintegral_congr_ae hzeroAE
      _ = 0 := lintegral_zero
      _ = ENNReal.ofReal (2 * (∫ x : ℝ, (max x 0)^4 ∂ν)^(1/4 : ℝ)) := by
        rw [← hMnat, hMzero]
        rw [Real.zero_rpow (by norm_num : (1 / 4 : ℝ) ≠ 0)]
        norm_num
      _ ≤ _ := le_rfl
  · have haPos : 0 < a := lt_of_le_of_ne ha0 (Ne.symm ha)
    have hMpow : a^4 = M := by
      dsimp [a]
      exact Real.rpow_inv_natCast_pow hM0 (by norm_num : (4 : ℕ) ≠ 0)
    have hMroot : M^(1/2 : ℝ) = a^2 := by
      rw [← hMpow, ← Real.rpow_natCast, ← Real.rpow_mul ha0]
      norm_num
    have hmarkovRoot (t : ℝ) (ht : 0 < t) : f t ≤ a^2 * t^(-2 : ℝ) := by
      dsimp [f]
      calc
        _ ≤ (M / t^(4 : ℝ))^(1/2 : ℝ) :=
          Real.rpow_le_rpow measureReal_nonneg (hmarkov t ht)
            (by norm_num : (0 : ℝ) ≤ 1 / 2)
        _ = M^(1/2 : ℝ) * t^(-2 : ℝ) := by
          rw [Real.div_rpow hM0 (Real.rpow_nonneg ht.le (4 : ℝ)) (1/2 : ℝ),
            ← Real.rpow_mul ht.le, div_eq_mul_inv, ← Real.rpow_neg ht.le]
          congr 2
          ring
        _ = a^2 * t^(-2 : ℝ) := by rw [hMroot]
    have hsmallConst : Integrable (fun _ : ℝ => (1 : ℝ))
        (volume.restrict (Ioc (0 : ℝ) a)) :=
      (integrableOn_const (μ := volume) (s := Ioc (0 : ℝ) a) (C := (1 : ℝ))
        (by simp)).integrable
    have hsmall : IntegrableOn f (Ioc (0 : ℝ) a) := by
      change Integrable f (volume.restrict (Ioc (0 : ℝ) a))
      apply hsmallConst.mono' hfMeas.aestronglyMeasurable.restrict
      filter_upwards with t
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 t)]
      simpa only [Real.one_rpow] using hfLeOne t
    have hpower : IntegrableOn (fun t : ℝ => t^(-2 : ℝ)) (Ioi a) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) haPos
    have hlarge : IntegrableOn f (Ioi a) := by
      apply (hpower.const_mul (a^2)).mono' hfMeas.aestronglyMeasurable.restrict
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 t)]
      exact hmarkovRoot t (lt_trans haPos ht)
    have hfull : IntegrableOn f (Ioi (0 : ℝ)) := by
      simpa only [Ioc_union_Ioi_eq_Ioi ha0] using hsmall.union hlarge
    have hsmallBound : (∫ t in Ioc (0 : ℝ) a, f t ∂volume) ≤ a := by
      calc
        _ ≤ ∫ t in Ioc (0 : ℝ) a, (1 : ℝ) ∂volume :=
          integral_mono_ae hsmall hsmallConst (Eventually.of_forall fun t => hfLeOne t)
        _ = ∫ t in (0 : ℝ)..a, (1 : ℝ) ∂volume :=
          (intervalIntegral.integral_of_le ha0).symm
        _ = a := by simp
    have hlargeBound : (∫ t in Ioi a, f t ∂volume) ≤ a := by
      calc
        _ ≤ ∫ t in Ioi a, a^2 * t^(-2 : ℝ) ∂volume := by
          apply integral_mono_ae hlarge (hpower.const_mul (a^2))
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          exact hmarkovRoot t (lt_trans haPos ht)
        _ = a^2 * ∫ t in Ioi a, t^(-2 : ℝ) ∂volume := by rw [integral_const_mul]
        _ = a := by
          rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) haPos]
          norm_num
          rw [Real.rpow_neg haPos.le 1, Real.rpow_one]
          field_simp [ne_of_gt haPos]
    have hsplit : (∫ t in Ioi (0 : ℝ), f t ∂volume) =
        (∫ t in Ioc (0 : ℝ) a, f t ∂volume) + (∫ t in Ioi a, f t ∂volume) := by
      rw [← Ioc_union_Ioi_eq_Ioi ha0]
      exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hsmall hlarge
    have hrealBound : (∫ t in Ioi (0 : ℝ), f t ∂volume) ≤ 2*a := by
      rw [hsplit]
      linarith only [hsmallBound, hlargeBound]
    have hrealFinal : (∫ t in Ioi (0 : ℝ), f t ∂volume) ≤
        2 * (∫ x : ℝ, (max x 0)^4 ∂ν)^(1/4 : ℝ) := by
      rw [← haTarget]
      exact hrealBound
    have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hf0 t
    calc
      _ = ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (f t) ∂volume := by
        apply lintegral_congr
        intro t
        exact htailENN t
      _ = ENNReal.ofReal (∫ t in Ioi (0 : ℝ), f t ∂volume) :=
        (ofReal_integral_eq_lintegral_ofReal hfull hnonneg).symm
      _ ≤ ENNReal.ofReal (2 * (∫ x : ℝ, (max x 0)^4 ∂ν)^(1/4 : ℝ)) :=
        ENNReal.ofReal_le_ofReal hrealFinal

end LPPDifferentiability
