/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Probability.EnvironmentMap
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# The law of the negated weight field

Martin (2004), Section 2, remarks that replacing each weight `X(z)` by `-X(z)` only changes the
sign of the passage time. This file proves the law-level facts behind that remark:
the negated environment, the reflected one-site tails, the swapped integrated square-root tail
conditions (2.6) and (2.7), and the sign change of the mean with no change of the variance.

Notation: `μ.map Neg.neg` is the law of `-X` when `X` has law `μ`. The tail sets are the
standard half-lines `Ioi`, `Iio`, `Ici` and `Iic` of the real line.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LPPDifferentiability

/-- Negation is a measurable map on the real line. -/
private theorem measurable_neg_real : Measurable (Neg.neg : ℝ → ℝ) := measurable_neg

/-- Negating every site of the canonical environment gives the canonical environment of the
negated one-site law. Source: the i.i.d. weight setup of Martin (2004), Section 2, and the sign
change described there. -/
theorem environmentLaw_negated_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (environmentLaw μ).map (fun ω : Environment => fun z : Lattice => -ω z) =
      environmentLaw (μ.map Neg.neg) :=
  environmentLaw_map_coordinatewise μ Neg.neg measurable_neg_real

/-- The one-site marginal of the negated environment is the negated one-site law. Source:
Martin (2004), Section 2, as in `environmentLaw_negated_eq`. -/
theorem environmentLaw_negated_eval (μ : Measure ℝ) [IsProbabilityMeasure μ] (z : Lattice) :
    (environmentLaw μ).map (fun ω : Environment => -ω z) = μ.map Neg.neg :=
  environmentLaw_map_coordinatewise_eval μ Neg.neg measurable_neg_real z

/-- The strict upper tail of the negated law is the strict lower tail of the original law:
`P(-X > t) = P(X < -t)`. Source: Martin (2004), Section 2 (sign change) and the tail
conditions (2.6) and (2.7). -/
theorem negated_law_Ioi (μ : Measure ℝ) (t : ℝ) :
    (μ.map Neg.neg) (Ioi t) = μ (Iio (-t)) := by
  rw [Measure.map_apply measurable_neg_real measurableSet_Ioi]
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_Iio]
  constructor <;> intro h <;> linarith

/-- The strict lower tail of the negated law is the strict upper tail of the original law:
`P(-X < t) = P(X > -t)`. Source: Martin (2004), Section 2 (sign change). -/
theorem negated_law_Iio (μ : Measure ℝ) (t : ℝ) :
    (μ.map Neg.neg) (Iio t) = μ (Ioi (-t)) := by
  rw [Measure.map_apply measurable_neg_real measurableSet_Iio]
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_Iio]
  constructor <;> intro h <;> linarith

/-- The closed upper tail of the negated law is the closed lower tail of the original law:
`P(-X >= t) = P(X <= -t)`. Source: Martin (2004), Section 2 (sign change). -/
theorem negated_law_Ici (μ : Measure ℝ) (t : ℝ) :
    (μ.map Neg.neg) (Ici t) = μ (Iic (-t)) := by
  rw [Measure.map_apply measurable_neg_real measurableSet_Ici]
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_Iic]
  constructor <;> intro h <;> linarith

/-- The closed lower tail of the negated law is the closed upper tail of the original law:
`P(-X <= t) = P(X >= -t)`. This is the closed form of the cumulative distribution function of
`-X`. Source: Martin (2004), Section 2 (distribution function F(s) = P(X <= s) and the sign
change). -/
theorem negated_law_Iic (μ : Measure ℝ) (t : ℝ) :
    (μ.map Neg.neg) (Iic t) = μ (Ici (-t)) := by
  rw [Measure.map_apply measurable_neg_real measurableSet_Iic]
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_Iic]
  constructor <;> intro h <;> linarith

/-- An atom of the negated law sits at the negated point: `P(-X = t) = P(X = -t)`. Source:
Martin (2004), Section 2 (the tails may have atoms) and the sign change there. -/
theorem negated_law_singleton (μ : Measure ℝ) (t : ℝ) :
    (μ.map Neg.neg) {t} = μ {-t} := by
  rw [Measure.map_apply measurable_neg_real (measurableSet_singleton t)]
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  exact neg_eq_iff_eq_neg

/-- Almost every point of the line is not an atom: for every finite measure, the set of
points carrying an atom is countable, so `μ {u} = 0` for Lebesgue-almost every `u`. This is
the step that lets the paper's integrals over `(1 - F)` and `F` use either endpoint convention.
Source: Martin (2004), Section 2. -/
private theorem ae_singleton_eq_zero (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∀ᵐ u ∂(volume : Measure ℝ), μ {u} = 0 := by
  rw [ae_iff]
  have hcount : Set.Countable {u : ℝ | 0 < μ {u}} := by
    simpa using Measure.countable_meas_level_set_pos (μ := μ) (g := fun u : ℝ => u)
      measurable_id
  refine measure_mono_null (fun u hu => ?_) (hcount.measure_zero volume)
  exact pos_iff_ne_zero.2 hu

/-- Almost everywhere, the closed and strict lower tails of `μ` agree at each point. -/
private theorem ae_Iio_eq_Iic (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∀ᵐ u ∂(volume : Measure ℝ), μ (Iio u) = μ (Iic u) := by
  filter_upwards [ae_singleton_eq_zero μ] with u hu
  have hdisj : Disjoint (Iio u) {u} := Set.disjoint_singleton_right.2 (by simp)
  rw [← Iio_union_right, measure_union hdisj (measurableSet_singleton u), hu, add_zero]

/-- Almost everywhere, the closed and strict upper tails of `μ` agree at each point. -/
private theorem ae_Ici_eq_Ioi (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∀ᵐ u ∂(volume : Measure ℝ), μ (Ici u) = μ (Ioi u) := by
  filter_upwards [ae_singleton_eq_zero μ] with u hu
  have hset : Ici u = Ioi u ∪ {u} := by
    ext x
    simp only [Set.mem_Ici, Set.mem_union, Set.mem_Ioi, Set.mem_singleton_iff]
    constructor
    · intro h
      rcases eq_or_lt_of_le h with h | h
      · exact Or.inr h.symm
      · exact Or.inl h
    · rintro (h | h)
      · exact le_of_lt h
      · exact le_of_eq h.symm
  have hdisj : Disjoint (Ioi u) {u} := Set.disjoint_singleton_right.2 (by simp)
  rw [hset, measure_union hdisj (measurableSet_singleton u), hu, add_zero]

/-- Reflection of a half-line integral at zero: the integral over `(0, ∞)` of `F(-t)` equals
the integral over `(-∞, 0)` of `F`, for measurable `F` with values in `[0, ∞]`. -/
private theorem lintegral_restrict_neg {F : ℝ → ℝ≥0∞} (hF : Measurable F) {s : Set ℝ}
    (hs : MeasurableSet s) :
    ∫⁻ y in s, F y = ∫⁻ x in (fun x : ℝ => -x) ⁻¹' s, F (-x) := by
  conv_lhs => rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
  exact setLIntegral_map hs hF measurable_neg_real

/-- Reflection from `(0, ∞)` to `(-∞, 0)`. -/
private theorem lintegral_Ioi_neg {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ t in Ioi (0 : ℝ), F (-t) = ∫⁻ u in Iio (0 : ℝ), F u := by
  have hpre : (fun x : ℝ => -x) ⁻¹' Iio (0 : ℝ) = Ioi 0 := by
    ext x
    simp
  rw [lintegral_restrict_neg hF measurableSet_Iio, hpre]

/-- Reflection from `(-∞, 0)` to `(0, ∞)`. -/
private theorem lintegral_Iio_neg {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ t in Iio (0 : ℝ), F (-t) = ∫⁻ u in Ioi (0 : ℝ), F u := by
  have hpre : (fun x : ℝ => -x) ⁻¹' Ioi (0 : ℝ) = Iio 0 := by
    ext x
    simp
  rw [lintegral_restrict_neg hF measurableSet_Ioi, hpre]

/-- The upper square-root tail condition (2.6) for the negated law is the lower condition (2.7)
for the original law: `∫₀^∞ P(-X > t)^(1/2) dt < ∞` if and only if
`∫_{-∞}^0 P(X <= t)^(1/2) dt < ∞`. Source: Martin (2004), conditions (2.6) and (2.7), with the
sign change in Section 2. -/
theorem negated_upper_sqrt_tail_iff (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (∫⁻ t in Ioi (0 : ℝ), ((μ.map Neg.neg) (Ioi t)) ^ (1 / 2 : ℝ)) < ∞ ↔
      (∫⁻ t in Iio (0 : ℝ), (μ (Iic t)) ^ (1 / 2 : ℝ)) < ∞ := by
  have hmono : Monotone (fun u : ℝ => μ (Iio u)) := fun a b hab =>
    measure_mono (Iio_subset_Iio hab)
  have hmeas : Measurable (fun u : ℝ => (μ (Iio u)) ^ (1 / 2 : ℝ)) :=
    hmono.measurable.pow_const _
  have h1 : (∫⁻ t in Ioi (0 : ℝ), ((μ.map Neg.neg) (Ioi t)) ^ (1 / 2 : ℝ)) =
      ∫⁻ t in Ioi (0 : ℝ), (μ (Iio (-t))) ^ (1 / 2 : ℝ) :=
    setLIntegral_congr_fun measurableSet_Ioi (fun t _ => by simp only [negated_law_Ioi])
  have h2 : (∫⁻ u in Iio (0 : ℝ), (μ (Iio u)) ^ (1 / 2 : ℝ)) =
      ∫⁻ u in Iio (0 : ℝ), (μ (Iic u)) ^ (1 / 2 : ℝ) :=
    lintegral_congr_ae (ae_restrict_of_ae ((ae_Iio_eq_Iic μ).mono fun u hu => by simp only [hu]))
  rw [h1, lintegral_Ioi_neg hmeas, h2]

/-- The lower square-root tail condition (2.7) for the negated law is the upper condition (2.6)
for the original law: `∫_{-∞}^0 P(-X <= t)^(1/2) dt < ∞` if and only if
`∫₀^∞ P(X > t)^(1/2) dt < ∞`. Source: Martin (2004), conditions (2.6) and (2.7), with the
sign change in Section 2. -/
theorem negated_lower_sqrt_tail_iff (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (∫⁻ t in Iio (0 : ℝ), ((μ.map Neg.neg) (Iic t)) ^ (1 / 2 : ℝ)) < ∞ ↔
      (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞ := by
  have hanti : Antitone (fun u : ℝ => μ (Ici u)) := fun a b hab =>
    measure_mono (Ici_subset_Ici.2 hab)
  have hmeas : Measurable (fun u : ℝ => (μ (Ici u)) ^ (1 / 2 : ℝ)) :=
    hanti.measurable.pow_const _
  have h1 : (∫⁻ t in Iio (0 : ℝ), ((μ.map Neg.neg) (Iic t)) ^ (1 / 2 : ℝ)) =
      ∫⁻ t in Iio (0 : ℝ), (μ (Ici (-t))) ^ (1 / 2 : ℝ) :=
    setLIntegral_congr_fun measurableSet_Iio (fun t _ => by simp only [negated_law_Iic])
  have h2 : (∫⁻ u in Ioi (0 : ℝ), (μ (Ici u)) ^ (1 / 2 : ℝ)) =
      ∫⁻ u in Ioi (0 : ℝ), (μ (Ioi u)) ^ (1 / 2 : ℝ) :=
    lintegral_congr_ae (ae_restrict_of_ae ((ae_Ici_eq_Ioi μ).mono fun u hu => by simp only [hu]))
  rw [h1, lintegral_Iio_neg hmeas, h2]

/-- The mean changes sign: `E[-X] = -E[X]`. The identity needs no integrability hypothesis,
because both sides are zero when `X` is not integrable. Source: Martin (2004), Theorem 2.4
(the distribution F has mean µ) and the sign change in Section 2. -/
theorem negated_mean (μ : Measure ℝ) :
    ∫ x, x ∂(μ.map Neg.neg) = -∫ x, x ∂μ := by
  have hm : AEStronglyMeasurable (fun x : ℝ => x) (μ.map Neg.neg) :=
    measurable_id.aestronglyMeasurable
  rw [integral_map measurable_neg_real.aemeasurable hm]
  exact integral_neg (fun x : ℝ => x)

/-- The negated law is integrable exactly when the original law is. Source: Martin (2004),
Theorem 2.4 (the existence of the mean µ) and the sign change in Section 2. -/
theorem negated_integrable_iff (μ : Measure ℝ) :
    Integrable (fun x : ℝ => x) (μ.map Neg.neg) ↔ Integrable (fun x : ℝ => x) μ := by
  have hm : AEStronglyMeasurable (fun x : ℝ => x) (μ.map Neg.neg) :=
    measurable_id.aestronglyMeasurable
  rw [integrable_map_measure hm measurable_neg_real.aemeasurable]
  exact integrable_neg_iff (f := fun x : ℝ => x)

/-- The variance is unchanged by negation, in the centred-moment form
`∫ (t - mean)^2` used by the paper's variance `σ²` (Theorem 2.4). Source: Martin (2004),
Theorem 2.4 and the sign change in Section 2. -/
theorem negated_variance (μ : Measure ℝ) :
    ∫ t, (t - ∫ s, s ∂(μ.map Neg.neg)) ^ 2 ∂(μ.map Neg.neg) =
      ∫ t, (t - ∫ s, s ∂μ) ^ 2 ∂μ := by
  have hc : Continuous (fun t : ℝ => (t - -∫ s, s ∂μ) ^ 2) := by fun_prop
  rw [negated_mean, integral_map measurable_neg_real.aemeasurable hc.aestronglyMeasurable]
  congr 1
  funext x
  ring

end LPPDifferentiability
