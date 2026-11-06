/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.MeanVarianceTruncation
public import ProbabilityBasics.Probability.SqrtTailMoments
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# Lemma 4.3 of Martin (2004), lower tail and the two-sided statement

First, a lower-tail replacement moves mass below the cutoff to two points, preserving total mass,
mean, and second moment while leaving the law above the cutoff unchanged.
Applying the construction to both tails gives a bounded law with the same mean and variance.
The two square-root tail conditions allow an arbitrarily small integrated square-root CDF error.

* `martin_truncation_lower_tail` is the mirror image of the upper-tail construction of
  `MeanVarianceTruncation.lean`: the mass of `X` below `-t` is replaced by two atoms, one at `-t`
  and one at a point `u < -t`, keeping the conditional mean and second moment.
* `martin_truncation_mean_variance` is the two-sided form of Lemma 4.3. Truncate the upper tail at
  a level `t`, then truncate the lower tail of the result at `-t'`. The lower tail of the first
  result equals that of the original law, so the same smallness argument applies, and the two
  distances add by the triangle inequality for
  `|a - c| ^ (1/2) ≤ |a - b| ^ (1/2) + |b - c| ^ (1/2)`.

The hypotheses are exactly Martin's (2.6) and (2.7), in the forms `hpos` and `hneg` of
Martin (2004), Theorem 2.4. The finite second moment, which the end of the proof of Lemma 4.3
uses, comes from `sqrt_tail_integrable_sq`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace LPPDifferentiability

/-! ### The lower tail -/

/-- **Lemma 4.3, lower tail** (the mirror image of the upper tail in Martin (2004)).
For a probability measure `μ` with finite second moment and `t ≥ 0`, replacing the mass
below `-t` by two atoms gives a probability measure `ν` that is bounded below, equal to `μ`
above `-t`, has the same mean and second moment, and whose square-root distance from `μ` is at
most the integral of the square root of the lower tail below `-t` plus the square root of
`E (X ^ 2; X < -t)`. -/
theorem martin_truncation_lower_tail
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hsq : Integrable (fun x : ℝ => x ^ 2) μ)
    {t : ℝ} (ht : 0 ≤ t) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ (∃ L : ℝ, ∀ᵐ x ∂ν, L ≤ x) ∧
      ν.restrict (Ioi (-t)) = μ.restrict (Ioi (-t)) ∧
      Integrable (fun x : ℝ => x ^ 2) ν ∧
      ∫ x, x ∂ν = ∫ x, x ∂μ ∧ ∫ x, x ^ 2 ∂ν = ∫ x, x ^ 2 ∂μ ∧
      (∫⁻ s : ℝ, ENNReal.ofReal
          (|(μ (Iic s)).toReal - (ν (Iic s)).toReal| ^ (1 / 2 : ℝ))) ≤
        (∫⁻ s in Iio (-t), (μ (Iic s)) ^ (1 / 2 : ℝ)) +
          (∫⁻ x in Iio (-t), ENNReal.ofReal (x ^ 2) ∂μ) ^ (1 / 2 : ℝ) := by
  by_cases hP : μ (Iio (-t)) = 0
  · -- no mass below `-t`: the law already has a lower bound
    refine ⟨μ, inferInstance, ⟨-t, ?_⟩, rfl, hsq, rfl, rfl, ?_⟩
    · exact (measure_eq_zero_iff_ae_notMem.1 hP).mono fun x hx => not_lt.1 hx
    · have hzero : ∀ s : ℝ, ENNReal.ofReal
          (|(μ (Iic s)).toReal - (μ (Iic s)).toReal| ^ (1 / 2 : ℝ)) = 0 := fun s => by
        rw [sub_self, abs_zero, Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0),
          ENNReal.ofReal_zero]
      rw [lintegral_congr hzero, lintegral_zero]
      exact zero_le
  · obtain ⟨p, u, hp0, hp1, -, hdown, hpu, ν, hν, hprob, hsqν, hmean, hsecond⟩ :=
      martin_two_point_replacement μ hsq measurableSet_Iio hP (c := -t) (Or.inr subset_rfl)
    have hu : u < -t := hdown subset_rfl
    have hq0 : 0 < (μ (Iio (-t))).toReal := ENNReal.toReal_pos hP (measure_ne_top _ _)
    have hα : 0 ≤ (1 - p) * (μ (Iio (-t))).toReal := mul_nonneg (sub_nonneg.2 hp1) hq0.le
    have hβ : 0 ≤ p * (μ (Iio (-t))).toReal := mul_nonneg hp0.le hq0.le
    have hν' : ν = μ.restrict (Ici (-t)) +
        ENNReal.ofReal ((1 - p) * (μ (Iio (-t))).toReal) • Measure.dirac (-t) +
          ENNReal.ofReal (p * (μ (Iio (-t))).toReal) • Measure.dirac u := by
      rw [hν, compl_Iio]
    -- the two atoms carry exactly the mass that was removed
    have hsum : ENNReal.ofReal ((1 - p) * (μ (Iio (-t))).toReal) +
        ENNReal.ofReal (p * (μ (Iio (-t))).toReal) = μ (Iio (-t)) := by
      rw [← ENNReal.ofReal_add hα hβ,
        show (1 - p) * (μ (Iio (-t))).toReal + p * (μ (Iio (-t))).toReal =
          (μ (Iio (-t))).toReal by ring,
        ENNReal.ofReal_toReal (measure_ne_top _ _)]
    -- from `-t` on, the distribution functions agree
    have hcdf : ∀ s : ℝ, -t ≤ s → ν (Iic s) = μ (Iic s) := by
      intro s hs
      have hdiff : Iic s \ Ici (-t) = Iio (-t) := by
        ext x
        simp only [Set.mem_sdiff, mem_Iic, mem_Ici, not_le, mem_Iio]
        exact ⟨fun h => h.2, fun h => ⟨h.le.trans hs, h⟩⟩
      rw [hν', martin_two_point_apply _ _ _ _ _ measurableSet_Iic,
        Measure.restrict_apply measurableSet_Iic, indicator_of_mem (mem_Iic.2 hs),
        indicator_of_mem (mem_Iic.2 (hu.le.trans hs)), Pi.one_apply, Pi.one_apply, mul_one,
        mul_one, add_assoc, hsum,
        ← measure_inter_add_sdiff (μ := μ) (Iic s) (measurableSet_Ici (a := -t)), hdiff]
    -- below `-t` the distribution function of `ν` is `p q` from `u` on and `0` before
    have hbtail : ∀ s : ℝ, s < -t → ν (Iic s) =
        ENNReal.ofReal (p * (μ (Iio (-t))).toReal) *
          Set.indicator (Iic s) (1 : ℝ → ℝ≥0∞) u := by
      intro s hs
      have hcn : -t ∉ Iic s := fun h => (not_le.2 hs) (mem_Iic.1 h)
      rw [hν', martin_two_point_apply _ _ _ _ _ measurableSet_Iic,
        Measure.restrict_apply measurableSet_Iic, Iic_inter_Ici, Icc_eq_empty_of_lt hs,
        measure_empty, indicator_of_notMem hcn]
      simp
    -- `ν` has no mass below `u`
    have hbdd : ∀ᵐ x ∂ν, u ≤ x := by
      have hempty : Iio u ∩ Ici (-t) = ∅ := eq_empty_of_forall_notMem fun x hx =>
        (not_le.2 ((mem_Iio.1 hx.1).trans hu)) (mem_Ici.1 hx.2)
      have hcn : -t ∉ Iio u := fun h => (not_lt.2 hu.le) (mem_Iio.1 h)
      have hun : u ∉ Iio u := fun h => lt_irrefl u (mem_Iio.1 h)
      have h0 : ν (Iio u) = 0 := by
        rw [hν', martin_two_point_apply _ _ _ _ _ measurableSet_Iio,
          Measure.restrict_apply measurableSet_Iio, hempty, measure_empty,
          indicator_of_notMem hcn, indicator_of_notMem hun]
        simp
      exact (measure_eq_zero_iff_ae_notMem.1 h0).mono fun x hx => not_lt.1 hx
    -- `ν` and `μ` agree above `-t`
    have hagree : ν.restrict (Ioi (-t)) = μ.restrict (Ioi (-t)) := by
      refine Measure.ext fun S hS => ?_
      have hS' : MeasurableSet (S ∩ Ioi (-t)) := hS.inter measurableSet_Ioi
      have hcn : -t ∉ S ∩ Ioi (-t) := fun h => lt_irrefl (-t) (mem_Ioi.1 h.2)
      have hun : u ∉ S ∩ Ioi (-t) := fun h => (not_lt.2 hu.le) (mem_Ioi.1 h.2)
      rw [Measure.restrict_apply hS, Measure.restrict_apply hS, hν',
        martin_two_point_apply _ _ _ _ _ hS', Measure.restrict_apply hS',
        indicator_of_notMem hcn, indicator_of_notMem hun, mul_zero, mul_zero, add_zero, add_zero,
        inter_eq_left.2 (inter_subset_right.trans Ioi_subset_Ici_self)]
    refine ⟨ν, hprob, ⟨u, hbdd⟩, hagree, hsqν, hmean, hsecond, ?_⟩
    -- the distance estimate, mirror of the final estimate in the proof of Martin (2004), Lemma 4.3
    have hmeas : Measurable fun s : ℝ => μ (Iic s) ^ (1 / 2 : ℝ) :=
      Monotone.measurable fun _ _ hst =>
        ENNReal.rpow_le_rpow (measure_mono (Iic_subset_Iic.2 hst)) (by norm_num)
    have hpt : ∀ s : ℝ, ENNReal.ofReal
        (|(μ (Iic s)).toReal - (ν (Iic s)).toReal| ^ (1 / 2 : ℝ)) ≤
        (Iio (-t)).indicator (fun s => μ (Iic s) ^ (1 / 2 : ℝ) + ν (Iic s) ^ (1 / 2 : ℝ)) s := by
      intro s
      by_cases hs : -t ≤ s
      · have hzero : ENNReal.ofReal
            (|(μ (Iic s)).toReal - (ν (Iic s)).toReal| ^ (1 / 2 : ℝ)) = 0 := by
          rw [hcdf s hs, sub_self, abs_zero, Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0),
            ENNReal.ofReal_zero]
        rw [hzero]
        exact zero_le
      · rw [indicator_of_mem (mem_Iio.2 (not_le.1 hs))]
        exact martin_sqrt_cdf_dist_le_lower μ ν s
    -- the integral of the square root of the distribution function of `ν` over `[u, -t)`
    have hatom : ∫⁻ s in Iio (-t), ν (Iic s) ^ (1 / 2 : ℝ) =
        ENNReal.ofReal (p * (μ (Iio (-t))).toReal) ^ (1 / 2 : ℝ) * ENNReal.ofReal (-t - u) := by
      have hcongr : ∫⁻ s in Iio (-t), ν (Iic s) ^ (1 / 2 : ℝ) =
          ∫⁻ s in Iio (-t), (Ici u).indicator
            (fun _ : ℝ => ENNReal.ofReal (p * (μ (Iio (-t))).toReal) ^ (1 / 2 : ℝ)) s := by
        refine setLIntegral_congr_fun measurableSet_Iio fun s hs => ?_
        rw [hbtail s (mem_Iio.1 hs)]
        by_cases hus : u ≤ s
        · rw [indicator_of_mem (show u ∈ Iic s from hus),
            indicator_of_mem (show s ∈ Ici u from hus), Pi.one_apply, mul_one]
        · rw [indicator_of_notMem (show u ∉ Iic s from fun h => hus (mem_Iic.1 h)),
            indicator_of_notMem (show s ∉ Ici u from fun h => hus (mem_Ici.1 h)), mul_zero,
            ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      rw [hcongr, lintegral_indicator measurableSet_Ici, setLIntegral_const,
        Measure.restrict_apply measurableSet_Ici, Ici_inter_Iio, Real.volume_Ico]
    have hd : -t - u ≤ |u| := by
      have hu0 : u < 0 := hu.trans_le (by linarith)
      rw [abs_of_neg hu0]
      linarith
    calc ∫⁻ s : ℝ, ENNReal.ofReal (|(μ (Iic s)).toReal - (ν (Iic s)).toReal| ^ (1 / 2 : ℝ))
        ≤ ∫⁻ s : ℝ, (Iio (-t)).indicator
            (fun s => μ (Iic s) ^ (1 / 2 : ℝ) + ν (Iic s) ^ (1 / 2 : ℝ)) s := lintegral_mono hpt
      _ = ∫⁻ s in Iio (-t), (μ (Iic s) ^ (1 / 2 : ℝ) + ν (Iic s) ^ (1 / 2 : ℝ)) :=
          lintegral_indicator measurableSet_Iio _
      _ = (∫⁻ s in Iio (-t), μ (Iic s) ^ (1 / 2 : ℝ)) +
            ∫⁻ s in Iio (-t), ν (Iic s) ^ (1 / 2 : ℝ) := lintegral_add_left hmeas _
      _ ≤ (∫⁻ s in Iio (-t), μ (Iic s) ^ (1 / 2 : ℝ)) +
            (∫⁻ x in Iio (-t), ENNReal.ofReal (x ^ 2) ∂μ) ^ (1 / 2 : ℝ) := by
          rw [hatom]
          exact add_le_add le_rfl
            (martin_atom_sqrt_le μ hsq (mul_nonneg hp0.le hq0.le) hpu hd)

/-! ### Tails tend to zero -/

/-- The tail integral over `(t, ∞)` of an integrable function tends to zero as `t → ∞`
(dominated convergence for the indicators of `(t, ∞)`). -/
private lemma tendsto_lintegral_Ioi_atTop (κ : Measure ℝ) {f : ℝ → ℝ≥0∞} (hf : Measurable f)
    (hfin : ∫⁻ x, f x ∂κ ≠ ∞) :
    Tendsto (fun t : ℝ => ∫⁻ x in Ioi t, f x ∂κ) atTop (𝓝 0) := by
  have hpt : ∀ x : ℝ, Tendsto (fun t : ℝ => (Ioi t).indicator f x) atTop (𝓝 0) := fun x =>
    tendsto_const_nhds.congr' (by
      filter_upwards [eventually_ge_atTop x] with t ht
      exact (indicator_of_notMem (fun h => (not_lt.2 ht) (mem_Ioi.1 h)) f).symm)
  have h : Tendsto (fun t : ℝ => ∫⁻ x, (Ioi t).indicator f x ∂κ) atTop
      (𝓝 (∫⁻ x, (0 : ℝ≥0∞) ∂κ)) :=
    tendsto_lintegral_filter_of_dominated_convergence f
      (Eventually.of_forall fun t => hf.indicator measurableSet_Ioi)
      (Eventually.of_forall fun t => Eventually.of_forall fun x => indicator_le_self _ _ x)
      hfin (Eventually.of_forall hpt)
  have e : (fun t : ℝ => ∫⁻ x in Ioi t, f x ∂κ) = fun t => ∫⁻ x, (Ioi t).indicator f x ∂κ :=
    funext fun t => (lintegral_indicator measurableSet_Ioi f).symm
  rw [e]
  rwa [lintegral_zero] at h

/-- The tail integral over `(-∞, t)` of an integrable function tends to zero as `t → -∞`. -/
private lemma tendsto_lintegral_Iio_atBot (κ : Measure ℝ) {f : ℝ → ℝ≥0∞} (hf : Measurable f)
    (hfin : ∫⁻ x, f x ∂κ ≠ ∞) :
    Tendsto (fun t : ℝ => ∫⁻ x in Iio t, f x ∂κ) atBot (𝓝 0) := by
  have hpt : ∀ x : ℝ, Tendsto (fun t : ℝ => (Iio t).indicator f x) atBot (𝓝 0) := fun x =>
    tendsto_const_nhds.congr' (by
      filter_upwards [eventually_le_atBot x] with t ht
      exact (indicator_of_notMem (fun h => (not_lt.2 ht) (mem_Iio.1 h)) f).symm)
  have h : Tendsto (fun t : ℝ => ∫⁻ x, (Iio t).indicator f x ∂κ) atBot
      (𝓝 (∫⁻ x, (0 : ℝ≥0∞) ∂κ)) :=
    tendsto_lintegral_filter_of_dominated_convergence f
      (Eventually.of_forall fun t => hf.indicator measurableSet_Iio)
      (Eventually.of_forall fun t => Eventually.of_forall fun x => indicator_le_self _ _ x)
      hfin (Eventually.of_forall hpt)
  have e : (fun t : ℝ => ∫⁻ x in Iio t, f x ∂κ) = fun t => ∫⁻ x, (Iio t).indicator f x ∂κ :=
    funext fun t => (lintegral_indicator measurableSet_Iio f).symm
  rw [e]
  rwa [lintegral_zero] at h

/-! ### Small facts used in the final assembly -/

/-- Two measures that agree after restriction to `s` give the same mass to measurable subsets
of `s`. -/
private lemma measure_eq_of_restrict_eq {κ₁ κ₂ : Measure ℝ} {s S : Set ℝ}
    (hS : MeasurableSet S) (hSs : S ⊆ s) (h : κ₁.restrict s = κ₂.restrict s) : κ₁ S = κ₂ S :=
  calc κ₁ S = κ₁ (S ∩ s) := by rw [inter_eq_left.2 hSs]
    _ = κ₁.restrict s S := (Measure.restrict_apply hS).symm
    _ = κ₂.restrict s S := by rw [h]
    _ = κ₂ (S ∩ s) := Measure.restrict_apply hS
    _ = κ₂ S := by rw [inter_eq_left.2 hSs]

/-- The distribution function `s ↦ μ (Iic s)` is measurable. -/
private lemma measurable_cdf_toReal (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Measurable fun s : ℝ => (μ (Iic s)).toReal :=
  Monotone.measurable fun _ _ hab =>
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Iic_subset_Iic.2 hab))

/-- Pointwise triangle inequality for the square-root distance. -/
private lemma ofReal_rpow_abs_sub_le (a b c : ℝ) :
    ENNReal.ofReal (|a - c| ^ (1 / 2 : ℝ)) ≤
      ENNReal.ofReal (|a - b| ^ (1 / 2 : ℝ)) + ENNReal.ofReal (|b - c| ^ (1 / 2 : ℝ)) := by
  have h1 : |a - c| ≤ |a - b| + |b - c| := abs_sub_le a b c
  calc ENNReal.ofReal (|a - c| ^ (1 / 2 : ℝ))
      ≤ ENNReal.ofReal ((|a - b| + |b - c|) ^ (1 / 2 : ℝ)) :=
        ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (abs_nonneg _) h1 (by norm_num))
    _ ≤ ENNReal.ofReal (|a - b| ^ (1 / 2 : ℝ) + |b - c| ^ (1 / 2 : ℝ)) :=
        ENNReal.ofReal_le_ofReal
          (Real.rpow_add_le_add_rpow (abs_nonneg _) (abs_nonneg _) (by norm_num) (by norm_num))
    _ = ENNReal.ofReal (|a - b| ^ (1 / 2 : ℝ)) + ENNReal.ofReal (|b - c| ^ (1 / 2 : ℝ)) :=
        ENNReal.ofReal_add (Real.rpow_nonneg (abs_nonneg _) _) (Real.rpow_nonneg (abs_nonneg _) _)

/-- Triangle inequality for the square-root distance of distribution functions. -/
private lemma sqrt_dist_triangle (μ ν₁ ν₂ : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν₁]
    [IsFiniteMeasure ν₂] :
    (∫⁻ s : ℝ, ENNReal.ofReal (|(μ (Iic s)).toReal - (ν₂ (Iic s)).toReal| ^ (1 / 2 : ℝ))) ≤
      (∫⁻ s : ℝ, ENNReal.ofReal (|(μ (Iic s)).toReal - (ν₁ (Iic s)).toReal| ^ (1 / 2 : ℝ))) +
      ∫⁻ s : ℝ, ENNReal.ofReal (|(ν₁ (Iic s)).toReal - (ν₂ (Iic s)).toReal| ^ (1 / 2 : ℝ)) := by
  have hmeas : Measurable fun s : ℝ =>
      ENNReal.ofReal (|(μ (Iic s)).toReal - (ν₁ (Iic s)).toReal| ^ (1 / 2 : ℝ)) :=
    Measurable.ennreal_ofReal (Measurable.pow_const
      (Measurable.abs (Measurable.sub (measurable_cdf_toReal μ) (measurable_cdf_toReal ν₁))) _)
  rw [← lintegral_add_left hmeas]
  exact lintegral_mono fun s => ofReal_rpow_abs_sub_le _ _ _

/-- The variance is the second moment minus the square of the mean. -/
private lemma integral_sq_sub_mean_sq (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun x : ℝ => x ^ 2) ν) :
    ∫ x, (x - ∫ s, s ∂ν) ^ 2 ∂ν = ∫ x, x ^ 2 ∂ν - (∫ x, x ∂ν) ^ 2 := by
  have hX : MemLp (fun x : ℝ => x) 2 ν :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2 hsq
  exact (ProbabilityTheory.variance_eq_integral (X := fun x : ℝ => x)
    measurable_id.aemeasurable).symm.trans (ProbabilityTheory.variance_eq_sub hX)

/-! ### Lemma 4.3, both tails -/

/-- **Martin (2004), Lemma 4.3, for both tails.**
Let `μ` be a probability measure satisfying the square-root tail conditions (2.6) (`hpos`) and
(2.7) (`hneg`), and let `ε > 0`. Then there is a probability measure `ν` with bounded support,
the same mean and the same variance as `μ`, such that the integral over the whole line of
`|F (s) - F~ (s)| ^ (1/2)`, where `F s = μ (Iic s)` and `F~ s = ν (Iic s)`, is less than `ε`.

Proof as in Martin (2004): truncate the upper tail at a level `t` (the two-atom replacement of
Lemma 4.3) so that the distance is below `ε/2`, then truncate the lower tail of the result at
`-t'` so that the distance is below `ε/2`; the distances add by the triangle inequality. -/
theorem martin_truncation_mean_variance
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : (∫⁻ t in Iio (0 : ℝ), (μ (Iic t)) ^ (1 / 2 : ℝ)) < ∞)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
      (∃ L : ℝ, ∀ᵐ x ∂ν, |x| ≤ L) ∧
      ∫ x, x ∂ν = ∫ x, x ∂μ ∧
      ∫ x, (x - ∫ s, s ∂ν) ^ 2 ∂ν = ∫ x, (x - ∫ s, s ∂μ) ^ 2 ∂μ ∧
      (∫⁻ s : ℝ, ENNReal.ofReal
          (|(μ (Iic s)).toReal - (ν (Iic s)).toReal| ^ (1 / 2 : ℝ))) < ENNReal.ofReal ε := by
  -- the second moment is finite, as at the end of the proof of Martin (2004), Lemma 4.3
  have hsq : Integrable (fun x : ℝ => x ^ 2) μ := sqrt_tail_integrable_sq μ hneg hpos
  have hε2 : 0 < ENNReal.ofReal ε / 2 := ENNReal.half_pos (ENNReal.ofReal_pos.2 hε).ne'
  have hsqfin : ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂μ ≠ ∞ :=
    ((hasFiniteIntegral_iff_ofReal (f := fun x : ℝ => x ^ 2)
      (Eventually.of_forall fun x => sq_nonneg x)).1 hsq.hasFiniteIntegral).ne
  have hsqmeas : Measurable fun x : ℝ => ENNReal.ofReal (x ^ 2) :=
    (by fun_prop : Measurable fun x : ℝ => x ^ 2).ennreal_ofReal
  have hmeasU : Measurable fun s : ℝ => μ (Ioi s) ^ (1 / 2 : ℝ) :=
    Antitone.measurable fun _ _ hst =>
      ENNReal.rpow_le_rpow (measure_mono (Ioi_subset_Ioi hst)) (by norm_num)
  have hmeasL : Measurable fun s : ℝ => μ (Iic s) ^ (1 / 2 : ℝ) :=
    Monotone.measurable fun _ _ hst =>
      ENNReal.rpow_le_rpow (measure_mono (Iic_subset_Iic.2 hst)) (by norm_num)
  -- the upper bound of the upper-tail step tends to zero as the level grows
  have hU1 : Tendsto (fun t : ℝ => ∫⁻ s in Ioi t, μ (Ioi s) ^ (1 / 2 : ℝ)) atTop (𝓝 0) :=
    (tendsto_lintegral_Ioi_atTop (volume.restrict (Ioi 0)) hmeasU hpos.ne).congr' (by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      rw [Measure.restrict_restrict measurableSet_Ioi, inter_eq_left.2 (Ioi_subset_Ioi ht)])
  have hU2 : Tendsto (fun t : ℝ => (∫⁻ x in Ioi t, ENNReal.ofReal (x ^ 2) ∂μ) ^ (1 / 2 : ℝ))
      atTop (𝓝 0) := by
    have h := ((ENNReal.continuous_rpow_const (y := 1 / 2)).tendsto 0).comp
      (tendsto_lintegral_Ioi_atTop μ hsqmeas hsqfin)
    rw [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h
    exact h
  have hU : Tendsto (fun t : ℝ => (∫⁻ s in Ioi t, μ (Ioi s) ^ (1 / 2 : ℝ)) +
      (∫⁻ x in Ioi t, ENNReal.ofReal (x ^ 2) ∂μ) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
    have h := hU1.add hU2
    rw [add_zero] at h
    exact h
  -- and likewise for the lower tail, as the level `-t'` goes to `-∞`
  have hL1' : Tendsto (fun t : ℝ => ∫⁻ s in Iio t, μ (Iic s) ^ (1 / 2 : ℝ)) atBot (𝓝 0) :=
    (tendsto_lintegral_Iio_atBot (volume.restrict (Iio 0)) hmeasL hneg.ne).congr' (by
      filter_upwards [eventually_le_atBot (0 : ℝ)] with t ht
      rw [Measure.restrict_restrict measurableSet_Iio, inter_eq_left.2 (Iio_subset_Iio ht)])
  have hL1 : Tendsto (fun t : ℝ => ∫⁻ s in Iio (-t), μ (Iic s) ^ (1 / 2 : ℝ)) atTop (𝓝 0) :=
    hL1'.comp tendsto_neg_atTop_atBot
  have hL2 : Tendsto (fun t : ℝ => (∫⁻ x in Iio (-t), ENNReal.ofReal (x ^ 2) ∂μ) ^ (1 / 2 : ℝ))
      atTop (𝓝 0) := by
    have h := ((ENNReal.continuous_rpow_const (y := 1 / 2)).tendsto 0).comp
      ((tendsto_lintegral_Iio_atBot μ hsqmeas hsqfin).comp tendsto_neg_atTop_atBot)
    rw [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h
    exact h
  have hL : Tendsto (fun t : ℝ => (∫⁻ s in Iio (-t), μ (Iic s) ^ (1 / 2 : ℝ)) +
      (∫⁻ x in Iio (-t), ENNReal.ofReal (x ^ 2) ∂μ) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
    have h := hL1.add hL2
    rw [add_zero] at h
    exact h
  -- choose the two levels
  obtain ⟨t, ht0, htU⟩ : ∃ t : ℝ, 0 ≤ t ∧ (∫⁻ s in Ioi t, μ (Ioi s) ^ (1 / 2 : ℝ)) +
      (∫⁻ x in Ioi t, ENNReal.ofReal (x ^ 2) ∂μ) ^ (1 / 2 : ℝ) < ENNReal.ofReal ε / 2 :=
    ((eventually_ge_atTop (0 : ℝ)).and (hU.eventually (gt_mem_nhds hε2))).exists
  obtain ⟨t', ht'0, ht'L⟩ : ∃ t' : ℝ, 0 ≤ t' ∧ (∫⁻ s in Iio (-t'), μ (Iic s) ^ (1 / 2 : ℝ)) +
      (∫⁻ x in Iio (-t'), ENNReal.ofReal (x ^ 2) ∂μ) ^ (1 / 2 : ℝ) < ENNReal.ofReal ε / 2 :=
    ((eventually_ge_atTop (0 : ℝ)).and (hL.eventually (gt_mem_nhds hε2))).exists
  -- first the upper tail of `μ`, then the lower tail of the result
  obtain ⟨ν₁, hp₁, ⟨L₁, hL₁⟩, hagree₁, hsq₁, hm₁, hs₁, hd₁⟩ :=
    martin_truncation_upper_tail μ hsq ht0
  have := hp₁
  obtain ⟨ν₂, hp₂, ⟨L₂, hL₂⟩, hagree₂, hsq₂, hm₂, hs₂, hd₂⟩ :=
    martin_truncation_lower_tail ν₁ hsq₁ ht'0
  have := hp₂
  -- below `-t'` the law `ν₁` is the law `μ`, so the lower-tail bound for `ν₁` is that for `μ`
  have hrestr : ν₁.restrict (Iio (-t')) = μ.restrict (Iio (-t')) := by
    refine Measure.ext fun S hS => ?_
    rw [Measure.restrict_apply hS, Measure.restrict_apply hS]
    exact measure_eq_of_restrict_eq (hS.inter measurableSet_Iio)
      (inter_subset_right.trans (Iio_subset_Iio (by linarith))) hagree₁
  have hcdf₁ : ∀ s : ℝ, s < -t' → ν₁ (Iic s) = μ (Iic s) := fun s hs =>
    measure_eq_of_restrict_eq measurableSet_Iic (Iic_subset_Iio.2 (by linarith)) hagree₁
  have hlow₁ : ∫⁻ s in Iio (-t'), ν₁ (Iic s) ^ (1 / 2 : ℝ) =
      ∫⁻ s in Iio (-t'), μ (Iic s) ^ (1 / 2 : ℝ) :=
    setLIntegral_congr_fun measurableSet_Iio fun s hs => by rw [hcdf₁ s (mem_Iio.1 hs)]
  have hsec₁ : ∫⁻ x in Iio (-t'), ENNReal.ofReal (x ^ 2) ∂ν₁ =
      ∫⁻ x in Iio (-t'), ENNReal.ofReal (x ^ 2) ∂μ := by rw [hrestr]
  rw [hlow₁, hsec₁] at hd₂
  -- bounded support
  have hnull : ν₂ (Ioi (max L₁ (-t'))) = 0 := by
    have h1 : ν₁ (Ioi (max L₁ (-t'))) = 0 :=
      measure_eq_zero_iff_ae_notMem.2 (hL₁.mono fun x hx hmem =>
        (not_lt.2 (hx.trans (le_max_left _ _))) (mem_Ioi.1 hmem))
    rw [measure_eq_of_restrict_eq (measurableSet_Ioi (a := max L₁ (-t')))
      (Ioi_subset_Ioi (le_max_right L₁ (-t'))) hagree₂]
    exact h1
  have hup : ∀ᵐ x ∂ν₂, x ≤ max L₁ (-t') :=
    (measure_eq_zero_iff_ae_notMem.1 hnull).mono fun x hx => not_lt.1 hx
  refine ⟨ν₂, hp₂, ⟨|L₂| + |max L₁ (-t')|, ?_⟩, hm₂.trans hm₁, ?_, ?_⟩
  · filter_upwards [hL₂, hup] with x hx1 hx2
    exact abs_le.2 ⟨by linarith [neg_abs_le L₂, abs_nonneg (max L₁ (-t'))],
      by linarith [le_abs_self (max L₁ (-t')), abs_nonneg L₂]⟩
  · -- the variance is the second moment minus the square of the mean
    rw [integral_sq_sub_mean_sq ν₂ hsq₂, integral_sq_sub_mean_sq μ hsq, hm₂.trans hm₁,
      hs₂.trans hs₁]
  · calc ∫⁻ s : ℝ, ENNReal.ofReal (|(μ (Iic s)).toReal - (ν₂ (Iic s)).toReal| ^ (1 / 2 : ℝ))
        ≤ (∫⁻ s : ℝ, ENNReal.ofReal (|(μ (Iic s)).toReal - (ν₁ (Iic s)).toReal| ^ (1 / 2 : ℝ))) +
          ∫⁻ s : ℝ, ENNReal.ofReal (|(ν₁ (Iic s)).toReal - (ν₂ (Iic s)).toReal| ^ (1 / 2 : ℝ)) :=
          sqrt_dist_triangle μ ν₁ ν₂
      _ ≤ ((∫⁻ s in Ioi t, μ (Ioi s) ^ (1 / 2 : ℝ)) +
            (∫⁻ x in Ioi t, ENNReal.ofReal (x ^ 2) ∂μ) ^ (1 / 2 : ℝ)) +
          ((∫⁻ s in Iio (-t'), μ (Iic s) ^ (1 / 2 : ℝ)) +
            (∫⁻ x in Iio (-t'), ENNReal.ofReal (x ^ 2) ∂μ) ^ (1 / 2 : ℝ)) :=
          add_le_add hd₁ hd₂
      _ < ENNReal.ofReal ε / 2 + ENNReal.ofReal ε / 2 := ENNReal.add_lt_add htU ht'L
      _ = ENNReal.ofReal ε := ENNReal.add_halves _

end LPPDifferentiability

end
