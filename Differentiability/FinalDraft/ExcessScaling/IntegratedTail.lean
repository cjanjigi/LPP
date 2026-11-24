/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.PositiveMomentTail
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-! Quantitative square-root tail integration at a real moment order greater than two. -/

public section

open MeasureTheory Filter Set
open scoped ENNReal

namespace LPPDifferentiability

/-- If the positive moment of order `p > 2` of a nonnegative random variable
is bounded by `a ^ p` for `a > 0`, its integrated square-root tail is at
most `a * (1 + (p / 2 - 1)⁻¹)`. This extends the split at Appendix B integrated-tail calculation to the
real exponent used at subsection `sub:ub_mom-chat`. -/
theorem integrated_sqrt_tail_le_of_rpow_moment_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → ℝ) (Y0 : ∀ ω, 0 ≤ Y ω) {p a : ℝ} (hp : 2 < p) (ha : 0 < a)
    (hInt : Integrable (fun ω => Y ω ^ p) μ)
    (hMoment : (∫ ω, Y ω ^ p ∂μ) ≤ a ^ p) :
    (∫⁻ t in Ioi (0 : ℝ), (μ {ω | t < Y ω}) ^ (1 / 2 : ℝ)) ≤
      ENNReal.ofReal (a * (1 + (p / 2 - 1)⁻¹)) := by
  let f : ℝ → ℝ≥0∞ := fun t => (μ {ω | t < Y ω}) ^ (1 / 2 : ℝ)
  have hp0 : 0 < p := by linarith only [hp]
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num

  -- Below the cutoff, the tail is bounded by one.
  have hsmall : (∫⁻ t in Ioc 0 a, f t) ≤ ENNReal.ofReal a := by
    calc
      _ ≤ ∫⁻ _ in Ioc (0 : ℝ) a, (1 : ℝ≥0∞) := by
        apply lintegral_mono
        intro t
        have hprob : μ {ω | t < Y ω} ≤ 1 :=
          (measure_mono (subset_univ _)).trans_eq measure_univ
        exact (ENNReal.rpow_le_rpow hprob hhalf).trans_eq (ENNReal.one_rpow _)
      _ = _ := by rw [setLIntegral_one, Real.volume_Ioc, sub_zero]

  -- Beyond the cutoff, Markov bounds the square-root tail by a power.
  have hlargePointwise (t : ℝ) (ht : 0 < t) :
      f t ≤ ENNReal.ofReal (a ^ (p / 2) * t ^ (-p / 2)) := by
    have hsub : {ω | t < Y ω} ⊆ {ω | t ^ p ≤ Y ω ^ p} := by
      intro ω hω
      exact Real.rpow_le_rpow ht.le (le_of_lt hω) hp0.le
    have hMarkov := mul_meas_ge_le_integral_of_nonneg
      (Eventually.of_forall fun ω => Real.rpow_nonneg (Y0 ω) p) hInt (t ^ p)
    have hdiv : μ.real {ω | t < Y ω} ≤ a ^ p / t ^ p := by
      apply (le_div_iff₀ (Real.rpow_pos_of_pos ht p)).2
      rw [mul_comm]
      exact (mul_le_mul_of_nonneg_left (measureReal_mono hsub)
        (Real.rpow_nonneg ht.le _)).trans (hMarkov.trans hMoment)
    have hroot := Real.rpow_le_rpow measureReal_nonneg hdiv hhalf
    dsimp [f]
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ {ω | t < Y ω}),
      ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hhalf]
    apply ENNReal.ofReal_le_ofReal
    change (μ.real {ω | t < Y ω}) ^ (1 / 2 : ℝ) ≤ _
    calc
      _ ≤ (a ^ p / t ^ p) ^ (1 / 2 : ℝ) := hroot
      _ = _ := by
        rw [Real.div_rpow (Real.rpow_nonneg ha.le _) (Real.rpow_nonneg ht.le _),
          ← Real.rpow_mul ha.le, ← Real.rpow_mul ht.le, div_eq_mul_inv,
          ← Real.rpow_neg ht.le]
        congr 2 <;> ring
  have hpTail : -p / 2 < -1 := by linarith only [hp]
  have hpower : IntegrableOn (fun t : ℝ => a ^ (p / 2) * t ^ (-p / 2)) (Ioi a) :=
    (integrableOn_Ioi_rpow_of_lt hpTail ha).const_mul _
  have hlarge : (∫⁻ t in Ioi a, f t) ≤ ENNReal.ofReal (a * (p / 2 - 1)⁻¹) := by
    calc
      _ ≤ ∫⁻ t in Ioi a, ENNReal.ofReal (a ^ (p / 2) * t ^ (-p / 2)) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact hlargePointwise t (ha.trans ht)
      _ = ENNReal.ofReal (∫ t in Ioi a, a ^ (p / 2) * t ^ (-p / 2)) := by
        symm
        apply ofReal_integral_eq_lintegral_ofReal hpower
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact mul_nonneg (Real.rpow_nonneg ha.le _) (Real.rpow_nonneg (ha.trans ht).le _)
      _ = _ := by
        congr 1
        rw [integral_const_mul, integral_Ioi_rpow_of_lt hpTail ha]
        have hdivide : -(a ^ (-p / 2 + 1)) / (-p / 2 + 1) =
            a ^ (-p / 2 + 1) * (p / 2 - 1)⁻¹ := by
          rw [show (-p / 2 + 1) = -(p / 2 - 1) by ring, neg_div_neg_eq]
          congr 1
        rw [hdivide, ← mul_assoc, ← Real.rpow_add ha,
          show p / 2 + (-p / 2 + 1) = 1 by ring, Real.rpow_one]

  -- Add the integrals on the two intervals.
  change (∫⁻ t in Ioi (0 : ℝ), f t) ≤ _
  rw [← Ioc_union_Ioi_eq_Ioi ha.le, lintegral_union measurableSet_Ioi Ioc_disjoint_Ioi_same]
  calc
    _ ≤ ENNReal.ofReal a + ENNReal.ofReal (a * (p / 2 - 1)⁻¹) := add_le_add hsmall hlarge
    _ = _ := by
      have hdenom : 0 ≤ p / 2 - 1 := by linarith only [hp]
      rw [← ENNReal.ofReal_add ha.le (mul_nonneg ha.le (inv_nonneg.mpr hdenom))]
      congr 1
      ring

end LPPDifferentiability
