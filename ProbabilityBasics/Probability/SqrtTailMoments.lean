/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Function.L1Space.HasFiniteIntegral
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Second moment from the integrated square-root tails

The finite second-moment estimate proved here is a step in the proof of Martin (2004), Lemma 4.3.
Under conditions (2.6) and (2.7), that lemma gives bounded-support approximations matching the
mean and variance, with small integrated square-root CDF distance. The hypotheses here use the
same forms (`hneg`, `hpos`) as the shape theorem.

The argument: with `a s` the square root of the tail at
`s`, the function `a` is nonincreasing, so `s * a s` is at most the integral of
`a` over `(0, s)`, which is at most the total integral `C`. Then `2 s` times
the tail is at most `2 C` times `a s`, and integrating gives a bound in terms
of `C` squared. The layer-cake formula turns the second moment into such an
integral, and the negative side is reduced to the positive side by reflection.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LPPDifferentiability

/-- For a nonincreasing `a` and `s > 0`, `s * a s` is at most the integral of `a`
over `(0, infinity)`. -/
private lemma ofReal_mul_le_lintegral_Ioi {a : ℝ → ℝ≥0∞} (ha : Antitone a) (s : ℝ) :
    ENNReal.ofReal s * a s ≤ ∫⁻ u in Ioi 0, a u := by
  calc ENNReal.ofReal s * a s
      = ∫⁻ _ in Ioc 0 s, a s := by
        rw [setLIntegral_const, Real.volume_Ioc, sub_zero, mul_comm]
    _ ≤ ∫⁻ u in Ioc 0 s, a u :=
        setLIntegral_mono' measurableSet_Ioc fun u hu => ha hu.2
    _ ≤ ∫⁻ u in Ioi 0, a u := lintegral_mono_set Ioc_subset_Ioi_self

/-- Core bound: if the square root of `p` is nonincreasing, the integral over
`(0, infinity)` of `p s * (2 s)` is at most `2 C * C`, where `C` is the integral of
the square root of `p` over `(0, infinity)`. -/
private lemma lintegral_mul_ofReal_two_mul_le {p : ℝ → ℝ≥0∞}
    (hp : Antitone fun s => p s ^ (1 / 2 : ℝ)) :
    ∫⁻ s in Ioi 0, p s * ENNReal.ofReal (2 * s) ≤
      ENNReal.ofReal 2 * (∫⁻ u in Ioi 0, p u ^ (1 / 2 : ℝ)) *
        ∫⁻ u in Ioi 0, p u ^ (1 / 2 : ℝ) := by
  set C := ∫⁻ u in Ioi 0, p u ^ (1 / 2 : ℝ) with hC
  have hbound : ∀ s ∈ Ioi (0 : ℝ),
      p s * ENNReal.ofReal (2 * s) ≤ ENNReal.ofReal 2 * C * p s ^ (1 / 2 : ℝ) := by
    intro s _
    have h1 : ENNReal.ofReal s * p s ^ (1 / 2 : ℝ) ≤ C :=
      ofReal_mul_le_lintegral_Ioi hp s
    have h2 : p s = p s ^ (1 / 2 : ℝ) * p s ^ (1 / 2 : ℝ) := by
      rw [← ENNReal.rpow_add_of_nonneg (1 / 2 : ℝ) (1 / 2 : ℝ) (by norm_num) (by norm_num)]
      norm_num
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    conv_lhs => rw [h2]
    calc p s ^ (1 / 2 : ℝ) * p s ^ (1 / 2 : ℝ) *
          (ENNReal.ofReal 2 * ENNReal.ofReal s)
        = ENNReal.ofReal 2 * (ENNReal.ofReal s * p s ^ (1 / 2 : ℝ)) *
            p s ^ (1 / 2 : ℝ) := by ring
      _ ≤ ENNReal.ofReal 2 * C * p s ^ (1 / 2 : ℝ) := by gcongr
  calc ∫⁻ s in Ioi 0, p s * ENNReal.ofReal (2 * s)
      ≤ ∫⁻ s in Ioi 0, ENNReal.ofReal 2 * C * p s ^ (1 / 2 : ℝ) :=
        setLIntegral_mono' measurableSet_Ioi hbound
    _ = ENNReal.ofReal 2 * C * C := by
        rw [lintegral_const_mul _ hp.measurable]

/-- The integral of `2 t` from `0` to `y` is `y ^ 2`. -/
private lemma integral_two_mul_interval (y : ℝ) :
    ∫ t in (0 : ℝ)..y, 2 * t = y ^ 2 := by
  rw [intervalIntegral.integral_const_mul, integral_id]
  ring

/-- Layer cake for a nonnegative measurable `f`: the integral of `(f x) ^ 2` is the
integral over `s > 0` of `mu {a | s < f a}` times `2 s`. -/
private lemma lintegral_sq_eq_layer (μ : Measure ℝ) (f : ℝ → ℝ) (hf : Measurable f)
    (hnn : ∀ x, 0 ≤ f x) :
    ∫⁻ x, ENNReal.ofReal ((f x) ^ 2) ∂μ =
      ∫⁻ s in Ioi 0, μ {a | s < f a} * ENNReal.ofReal (2 * s) := by
  have h := lintegral_comp_eq_lintegral_meas_lt_mul μ (f := f) (g := fun t : ℝ => 2 * t)
    (Eventually.of_forall fun x => hnn x) hf.aemeasurable
    (fun t _ => (by fun_prop : Continuous fun t : ℝ => 2 * t).intervalIntegrable 0 t)
    ((ae_restrict_iff' measurableSet_Ioi).2
      (Eventually.of_forall fun t (ht : 0 < t) => by
        show (0 : ℝ) ≤ 2 * t
        linarith))
  simpa only [integral_two_mul_interval] using h

/-- For `t > 0`, the set of `a` with `t < max a 0` is the open ray `(t, infinity)`. -/
private lemma setOf_lt_max_zero {t : ℝ} (ht : 0 < t) :
    {a : ℝ | t < max a 0} = Ioi t := by
  ext a
  simp only [Set.mem_ofPred_eq, mem_Ioi, lt_max_iff, not_lt.2 ht.le, or_false]

/-- For `t > 0`, the set of `a` with `t < max (-a) 0` is the open ray `(-infinity, -t)`. -/
private lemma setOf_lt_max_neg_zero {t : ℝ} (ht : 0 < t) :
    {a : ℝ | t < max (-a) 0} = Iio (-t) := by
  ext a
  simp only [Set.mem_ofPred_eq, mem_Iio, lt_max_iff, not_lt.2 ht.le, or_false, lt_neg]

/-- Change of variable `t = -s`: the integral over `(0, infinity)` of `h (-t)` equals the
integral over `(-infinity, 0)` of `h`. -/
private lemma lintegral_Ioi_comp_neg (h : ℝ → ℝ≥0∞) :
    ∫⁻ t in Ioi 0, h (-t) = ∫⁻ t in Iio 0, h t := by
  have key := (Measure.measurePreserving_neg (volume : Measure ℝ)).lintegral_comp_emb
    (MeasurableEquiv.neg ℝ).measurableEmbedding (Set.indicator (Iio 0) h)
  have e1 : ∫⁻ t in Ioi 0, h (-t) = ∫⁻ t, (Iio 0).indicator h (-t) := by
    rw [← lintegral_indicator measurableSet_Ioi]
    refine lintegral_congr fun t => ?_
    by_cases ht : 0 < t
    · have hn : -t < 0 := by linarith
      simp [Set.indicator, ht, hn]
    · have hn : ¬ (-t < 0) := not_lt.2 (by linarith [not_lt.1 ht])
      simp [Set.indicator, ht, hn]
  rw [e1, key, lintegral_indicator measurableSet_Iio]

/-- The square root of `mu (Ioi s)` is nonincreasing in `s`. -/
private lemma antitone_sqrt_Ioi (μ : Measure ℝ) :
    Antitone fun s : ℝ => μ (Ioi s) ^ (1 / 2 : ℝ) :=
  fun _ _ hst => ENNReal.rpow_le_rpow (measure_mono (Ioi_subset_Ioi hst)) (by norm_num)

/-- The square root of `mu (Iic (-s))` is nonincreasing in `s`. -/
private lemma antitone_sqrt_Iic_neg (μ : Measure ℝ) :
    Antitone fun s : ℝ => μ (Iic (-s)) ^ (1 / 2 : ℝ) :=
  fun _ _ hst => ENNReal.rpow_le_rpow
    (measure_mono (Iic_subset_Iic.2 (neg_le_neg hst))) (by norm_num)

/-- The positive part of the square moment is finite under the positive tail condition. -/
private lemma lintegral_max_sq_lt_top (μ : Measure ℝ)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞) :
    ∫⁻ x, ENNReal.ofReal ((max x 0) ^ 2) ∂μ < ∞ := by
  refine (lintegral_sq_eq_layer μ (fun x => max x 0) (by fun_prop)
    (fun x => le_max_right x 0)).trans_lt ?_
  calc ∫⁻ s in Ioi 0, μ {a | s < max a 0} * ENNReal.ofReal (2 * s)
      = ∫⁻ s in Ioi 0, μ (Ioi s) * ENNReal.ofReal (2 * s) :=
        setLIntegral_congr_fun measurableSet_Ioi fun s hs => by
          simp only [setOf_lt_max_zero hs]
    _ ≤ ENNReal.ofReal 2 * (∫⁻ u in Ioi 0, μ (Ioi u) ^ (1 / 2 : ℝ)) *
          ∫⁻ u in Ioi 0, μ (Ioi u) ^ (1 / 2 : ℝ) :=
        lintegral_mul_ofReal_two_mul_le (antitone_sqrt_Ioi μ)
    _ < ∞ := ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hpos) hpos

/-- The negative part of the square moment is finite under the negative tail condition. -/
private lemma lintegral_max_neg_sq_lt_top (μ : Measure ℝ)
    (hneg : (∫⁻ t in Iio (0 : ℝ), (μ (Iic t)) ^ (1 / 2 : ℝ)) < ∞) :
    ∫⁻ x, ENNReal.ofReal ((max (-x) 0) ^ 2) ∂μ < ∞ := by
  refine (lintegral_sq_eq_layer μ (fun x => max (-x) 0) (by fun_prop)
    (fun x => le_max_right (-x) 0)).trans_lt ?_
  have hC : ∫⁻ s in Ioi 0, μ (Iic (-s)) ^ (1 / 2 : ℝ) < ∞ := by
    rw [show (∫⁻ s in Ioi 0, μ (Iic (-s)) ^ (1 / 2 : ℝ)) =
        ∫⁻ t in Iio 0, μ (Iic t) ^ (1 / 2 : ℝ) from
          lintegral_Ioi_comp_neg (fun t => μ (Iic t) ^ (1 / 2 : ℝ))]
    exact hneg
  calc ∫⁻ s in Ioi 0, μ {a | s < max (-a) 0} * ENNReal.ofReal (2 * s)
      ≤ ∫⁻ s in Ioi 0, μ (Iic (-s)) * ENNReal.ofReal (2 * s) :=
        setLIntegral_mono' measurableSet_Ioi fun s hs => by
          simp only [setOf_lt_max_neg_zero hs]
          exact mul_le_mul_of_nonneg_right (measure_mono Iio_subset_Iic_self) zero_le
    _ ≤ ENNReal.ofReal 2 * (∫⁻ u in Ioi 0, μ (Iic (-u)) ^ (1 / 2 : ℝ)) *
          ∫⁻ u in Ioi 0, μ (Iic (-u)) ^ (1 / 2 : ℝ) :=
        lintegral_mul_ofReal_two_mul_le (antitone_sqrt_Iic_neg μ)
    _ < ∞ := ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC) hC

/-- **Second moment from the integrated square-root tails.** If the integral over `(-infinity, 0)`
of the square root of the lower tail `mu (Iic t)` is finite (Martin's condition (2.7), hypothesis
`hneg`), and the integral over `(0, infinity)` of the square root of the upper tail `mu (Ioi t)` is
finite (condition (2.6), hypothesis `hpos`), then `t ^ 2` is integrable for `mu`. This is a step in
the proof of Martin (2004), Lemma 4.3. -/
theorem sqrt_tail_integrable_sq (μ : Measure ℝ)
    (hneg : (∫⁻ t in Iio (0 : ℝ), (μ (Iic t)) ^ (1 / 2 : ℝ)) < ∞)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞) :
    Integrable (fun t : ℝ => t ^ 2) μ := by
  refine ⟨(by fun_prop : Continuous fun t : ℝ => t ^ 2).aestronglyMeasurable, ?_⟩
  refine (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun t => sq_nonneg t)).2 ?_
  have hpt : ∀ t : ℝ, ENNReal.ofReal (t ^ 2) ≤
      ENNReal.ofReal ((max t 0) ^ 2) + ENNReal.ofReal ((max (-t) 0) ^ 2) := by
    intro t
    rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    rcases le_total 0 t with h | h
    · rw [max_eq_left h, max_eq_right (neg_nonpos.2 h)]
      exact le_of_eq (by ring)
    · rw [max_eq_right h, max_eq_left (neg_nonneg.2 h)]
      exact le_of_eq (by ring)
  calc ∫⁻ t, ENNReal.ofReal (t ^ 2) ∂μ
      ≤ ∫⁻ t, (ENNReal.ofReal ((max t 0) ^ 2) + ENNReal.ofReal ((max (-t) 0) ^ 2)) ∂μ :=
        lintegral_mono hpt
    _ = ∫⁻ t, ENNReal.ofReal ((max t 0) ^ 2) ∂μ +
          ∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ 2) ∂μ :=
        lintegral_add_left (by fun_prop) _
    _ < ∞ := ENNReal.add_lt_top.2
        ⟨lintegral_max_sq_lt_top μ hpos, lintegral_max_neg_sq_lt_top μ hneg⟩

end LPPDifferentiability

end
