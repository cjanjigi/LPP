/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# The lower-tail example law

For `0 < α` there is a probability measure `μ` on the real line with
`μ (-∞, -t) = (1 + t) ^ (-α)` for `t ≥ 0`. It is the image of the uniform law
on `(0, 1]` under `u ↦ 1 - u ^ (-1 / α)`. From the tail formula alone we derive
that the weights are almost surely nonpositive, that `E[(w⁻) ^ p] < ∞` when
`0 < p < α`, and that `E w⁻ = ∞` when `α ≤ 1`. Here `w⁻ = max (-w) 0`, and the
expectations are extended-valued integrals.

This law is used in the lower-tail example of Appendix C (on the moment conditions) of the
differentiability preprint. The preprint states the two moment facts without proof; the
tail integrations here fill that omission.

## References

* C. Janjigian, F. Rassoul-Agha and T. Seppäläinen, *Differentiability of the shape function in the
  planar corner growth model*, preprint, Appendix C.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace LPPDifferentiability

/-- There is a probability law on the real line with lower tail
`μ (-∞, -t) = (1 + t) ^ (-α)` for all `t ≥ 0`. -/
theorem exists_lowerTail_law {α : ℝ} (hα : 0 < α) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧
      ∀ t : ℝ, 0 ≤ t → μ (Iio (-t)) = ENNReal.ofReal ((1 + t) ^ (-α)) := by
  set f : ℝ → ℝ := fun u => 1 - u ^ (-(1 / α)) with hf
  have hfm : Measurable f := measurable_const.sub (measurable_id.pow_const _)
  have hP : IsProbabilityMeasure (volume.restrict (Ioc (0 : ℝ) 1)) := ⟨by simp⟩
  refine ⟨(volume.restrict (Ioc (0 : ℝ) 1)).map f, inferInstance, ?_⟩
  intro t ht
  have hb0 : 0 < (1 + t) ^ (-α) := Real.rpow_pos_of_pos (by linarith) _
  have hb1 : (1 + t) ^ (-α) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hset : f ⁻¹' Iio (-t) ∩ Ioc 0 1 = Ioo 0 ((1 + t) ^ (-α)) := by
    ext u
    simp only [mem_inter_iff, mem_preimage, mem_Iio, mem_Ioc, mem_Ioo, hf]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h2, ?_⟩
      have h4 : 1 + t < u ^ (-(1 / α)) := by linarith
      have h5 : (u ^ (-(1 / α))) ^ (-α) < (1 + t) ^ (-α) :=
        Real.rpow_lt_rpow_of_neg (by linarith) h4 (by linarith)
      rw [← Real.rpow_mul h2.le] at h5
      have h6 : -(1 / α) * -α = 1 := by field_simp
      rwa [h6, Real.rpow_one] at h5
    · rintro ⟨h2, h3⟩
      have h5 : ((1 + t) ^ (-α)) ^ (-(1 / α)) < u ^ (-(1 / α)) :=
        Real.rpow_lt_rpow_of_neg h2 h3 (by simp [hα])
      rw [← Real.rpow_mul (by linarith)] at h5
      have h6 : -α * -(1 / α) = 1 := by field_simp
      rw [h6, Real.rpow_one] at h5
      exact ⟨by linarith, h2, h3.le.trans hb1⟩
  rw [Measure.map_apply hfm measurableSet_Iio, Measure.restrict_apply (hfm measurableSet_Iio),
    hset, Real.volume_Ioo, sub_zero]

/-- The tail formula makes the weight almost surely nonpositive. -/
theorem lowerTail_ae_nonpos (μ : Measure ℝ) [IsProbabilityMeasure μ] {α : ℝ}
    (htail : ∀ t : ℝ, 0 ≤ t → μ (Iio (-t)) = ENNReal.ofReal ((1 + t) ^ (-α))) :
    ∀ᵐ w ∂μ, w ≤ 0 := by
  have h0 : μ (Iio (0 : ℝ))ᶜ = 0 :=
    (prob_compl_eq_zero_iff measurableSet_Iio).2 (by simpa using htail 0 le_rfl)
  rw [ae_iff]
  refine measure_mono_null (fun w hw => ?_) h0
  simp only [mem_ofPred_eq, not_le] at hw
  simp only [mem_compl_iff, mem_Iio, not_lt]
  exact hw.le

private theorem lowerTail_measure_set {μ : Measure ℝ} {α : ℝ}
    (htail : ∀ t : ℝ, 0 ≤ t → μ (Iio (-t)) = ENNReal.ofReal ((1 + t) ^ (-α))) :
    ∀ t ∈ Ioi (0 : ℝ),
      μ {a : ℝ | t < max (-a) 0} = ENNReal.ofReal ((1 + t) ^ (-α)) := by
  intro t ht
  have ht0 : 0 < t := ht
  have hset : {a : ℝ | t < max (-a) 0} = Iio (-t) := by
    ext a
    simp only [mem_ofPred_eq, mem_Iio, lt_max_iff]
    constructor
    · rintro (h | h)
      · linarith
      · linarith
    · intro h
      exact Or.inl (by linarith)
  rw [hset]
  exact htail t ht0.le

/-- With `0 < p < α`, the `p`-th moment of the negative part is finite. -/
theorem lowerTail_lintegral_negPart_rpow_lt_top (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {p α : ℝ} (hp : 0 < p) (hpα : p < α)
    (htail : ∀ t : ℝ, 0 ≤ t → μ (Iio (-t)) = ENNReal.ofReal ((1 + t) ^ (-α))) :
    ∫⁻ w, ENNReal.ofReal ((max (-w) 0) ^ p) ∂μ < ∞ := by
  have hp' : p ≠ 0 := hp.ne'
  have hmeas : Measurable (fun w : ℝ => max (-w) 0) := measurable_neg.max measurable_const
  have hnn : 0 ≤ᵐ[μ] (fun w : ℝ => max (-w) 0) :=
    Filter.Eventually.of_forall (fun w => le_max_right _ _)
  have hg_int : ∀ t > (0 : ℝ), IntervalIntegrable (fun t : ℝ => p * t ^ (p - 1)) volume 0 t :=
    fun t _ => (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t)
      (by linarith)).const_mul p
  have hg_nn : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), 0 ≤ p * t ^ (p - 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg hp.le (Real.rpow_nonneg (le_of_lt ht) _)
  have hint : ∀ s : ℝ, ∫ t in (0 : ℝ)..s, p * t ^ (p - 1) = s ^ p := by
    intro s
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith)),
      sub_add_cancel, Real.zero_rpow hp', sub_zero]
    field_simp
  have hlc := lintegral_comp_eq_lintegral_meas_lt_mul μ hnn hmeas.aemeasurable hg_int hg_nn
  simp only [hint] at hlc
  have heq := setLIntegral_congr_fun (μ := volume) (s := Ioi (0 : ℝ)) measurableSet_Ioi
    (f := fun t => μ {a : ℝ | t < max (-a) 0} * ENNReal.ofReal (p * t ^ (p - 1)))
    (g := fun t => ENNReal.ofReal ((1 + t) ^ (-α)) * ENNReal.ofReal (p * t ^ (p - 1)))
    (fun t ht => by simp only [lowerTail_measure_set htail t ht])
  refine lt_of_eq_of_lt (hlc.trans heq) ?_
  have hsplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioi 1) :=
    disjoint_left.2 fun x hx hy => absurd hx.2 (not_le.2 hy)
  rw [hsplit, lintegral_union measurableSet_Ioi hdisj]
  refine ENNReal.add_lt_top.2 ⟨?_, ?_⟩
  · have hI : IntegrableOn (fun t : ℝ => p * t ^ (p - 1)) (Ioc 0 1) := (hg_int 1 one_pos).1
    calc ∫⁻ t in Ioc (0 : ℝ) 1,
          ENNReal.ofReal ((1 + t) ^ (-α)) * ENNReal.ofReal (p * t ^ (p - 1))
        ≤ ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (p * t ^ (p - 1)) := by
          apply setLIntegral_mono' measurableSet_Ioc
          intro t ht
          have h1 : (1 + t) ^ (-α) ≤ 1 :=
            Real.rpow_le_one_of_one_le_of_nonpos (by linarith [ht.1]) (by linarith)
          calc ENNReal.ofReal ((1 + t) ^ (-α)) * ENNReal.ofReal (p * t ^ (p - 1))
              ≤ 1 * ENNReal.ofReal (p * t ^ (p - 1)) :=
                mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_one.2 h1) zero_le
            _ = ENNReal.ofReal (p * t ^ (p - 1)) := one_mul _
      _ < ∞ := Integrable.lintegral_lt_top hI
  · have hI : IntegrableOn (fun t : ℝ => p * t ^ (p - 1 - α)) (Ioi 1) :=
      Integrable.const_mul (integrableOn_Ioi_rpow_of_lt (a := p - 1 - α) (by linarith)
        one_pos) p
    calc ∫⁻ t in Ioi (1 : ℝ),
          ENNReal.ofReal ((1 + t) ^ (-α)) * ENNReal.ofReal (p * t ^ (p - 1))
        ≤ ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (p * t ^ (p - 1 - α)) := by
          apply setLIntegral_mono' measurableSet_Ioi
          intro t ht
          have ht1 : 1 < t := ht
          have ht0 : (0 : ℝ) < t := lt_trans one_pos ht1
          have h1 : (1 + t) ^ (-α) ≤ t ^ (-α) :=
            Real.rpow_le_rpow_of_nonpos ht0 (by linarith) (by linarith)
          have h2 : t ^ (p - 1 - α) = t ^ (-α) * t ^ (p - 1) := by
            rw [← Real.rpow_add ht0]
            congr 1
            ring
          have h3 : p * t ^ (p - 1 - α) = t ^ (-α) * (p * t ^ (p - 1)) := by
            rw [h2]
            ring
          rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by linarith) _)]
          apply ENNReal.ofReal_le_ofReal
          rw [h3]
          exact mul_le_mul_of_nonneg_right h1
            (mul_nonneg hp.le (Real.rpow_nonneg ht0.le _))
      _ < ∞ := Integrable.lintegral_lt_top hI

/-- With `0 < α ≤ 1`, the first moment of the negative part is infinite. -/
theorem lowerTail_lintegral_negPart_eq_top (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (htail : ∀ t : ℝ, 0 ≤ t → μ (Iio (-t)) = ENNReal.ofReal ((1 + t) ^ (-α))) :
    ∫⁻ w, ENNReal.ofReal (max (-w) 0) ∂μ = ∞ := by
  have hmeas : Measurable (fun w : ℝ => max (-w) 0) := measurable_neg.max measurable_const
  have hnn : 0 ≤ᵐ[μ] (fun w : ℝ => max (-w) 0) :=
    Filter.Eventually.of_forall (fun w => le_max_right _ _)
  rw [lintegral_eq_lintegral_meas_lt μ hnn hmeas.aemeasurable,
    setLIntegral_congr_fun measurableSet_Ioi (lowerTail_measure_set htail)]
  by_contra hne
  have hm : AEStronglyMeasurable (fun t : ℝ => (1 + t) ^ (-α)) (volume.restrict (Ioi (0 : ℝ))) :=
    (measurable_const.add measurable_id |>.pow_const _).aestronglyMeasurable
  have hnn' : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] (fun t : ℝ => (1 + t) ^ (-α)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg (by linarith [mem_Ioi.1 ht]) _
  have hint : IntegrableOn (fun t : ℝ => (1 + t) ^ (-α)) (Ioi 0) :=
    (lintegral_ofReal_ne_top_iff_integrable hm hnn').1 hne
  have hint1 : IntegrableOn (fun t : ℝ => (1 + t) ^ (-α)) (Ioi 1) :=
    hint.mono_set (Ioi_subset_Ioi zero_le_one)
  have hint2 : IntegrableOn (fun t : ℝ => t ^ (-α)) (Ioi 1) := by
    refine Integrable.mono' (hint1.const_mul ((2 : ℝ) ^ α))
      (measurable_id.pow_const _).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : 1 < t := ht
    have ht0 : (0 : ℝ) < t := lt_trans one_pos ht1
    have h1 : (2 * t) ^ (-α) ≤ (1 + t) ^ (-α) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
    have h2 : (2 * t) ^ (-α) = (2 : ℝ) ^ (-α) * t ^ (-α) :=
      Real.mul_rpow (by norm_num) ht0.le
    have h3 : (2 : ℝ) ^ α * (2 : ℝ) ^ (-α) = 1 := by
      rw [← Real.rpow_add (by norm_num)]
      simp
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
    calc t ^ (-α) = (2 : ℝ) ^ α * ((2 : ℝ) ^ (-α) * t ^ (-α)) := by
          rw [← mul_assoc, h3, one_mul]
      _ = (2 : ℝ) ^ α * (2 * t) ^ (-α) := by rw [h2]
      _ ≤ (2 : ℝ) ^ α * (1 + t) ^ (-α) :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (by norm_num) _)
  have hlt := (integrableOn_Ioi_rpow_iff (s := -α) one_pos).1 hint2
  linarith

end LPPDifferentiability
