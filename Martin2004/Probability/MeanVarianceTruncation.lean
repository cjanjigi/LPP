/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Lemma 4.3 of Martin (2004), upper tail: replacing the mass above a level by two atoms

Martin (2004), Lemma 4.3, replaces the mass of a non-negative variable above a
level `t` by two atoms, one at `t` and one at a point `u > t`, chosen so that the
conditional mean and the conditional second moment above `t` are kept (equations
(4.3) and (4.4)). The new law has bounded support, the same mean and the same
variance, and is close to the old one in the square-root distance of distribution
functions.

This file has three parts.
* `martin_two_point_replacement` is the construction for any measurable set `A` of positive
  mass lying on one side of a point `c`. It is used for the upper tail here and for the
  negative tail (which Martin's proof only sketches) in `MeanVarianceTruncationTail.lean`.
* Pointwise bounds on the square root of the difference of two distribution functions.
* `martin_truncation_upper_tail`, the upper tail with the whole line in place of `X >= 0`.

Distributions are probability measures on the real line, `F s` is `mu (Iic s)`, and the integral of
a non-negative function over the line is the lower integral, as in the hypotheses `hneg` and `hpos`
of Martin (2004), Theorem 2.4.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LPPDifferentiability

/-! ### Preliminaries -/

/-- A real function `x ↦ x` is integrable for a finite measure when `x ↦ x ^ 2` is. -/
private lemma integrable_id_of_integrable_sq (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hsq : Integrable (fun x : ℝ => x ^ 2) μ) : Integrable (fun x : ℝ => x) μ := by
  refine Integrable.mono' (hsq.add (integrable_const (1 : ℝ)))
    measurable_id.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  simp only [Real.norm_eq_abs, Pi.add_apply]
  nlinarith [sq_abs x, sq_nonneg (|x| - 1), abs_nonneg x, sq_nonneg x]

/-- The solution of (4.3) and (4.4) of Martin (2004), Lemma 4.3, written for a conditional
mean `m` and conditional second moment `w` above the level `c` (or below it). The formulas
are `p = (m - c)^2 / ((m - c)^2 + w - m^2)` and `u = c + (m - c) / p`; the point `u`
lies on the same side of `c` as `m`. -/
private lemma exists_two_point_parameters {c m w : ℝ} (hne : m ≠ c) (hw : m ^ 2 ≤ w) :
    ∃ p u : ℝ, 0 < p ∧ p ≤ 1 ∧ (1 - p) * c + p * u = m ∧
      (1 - p) * c ^ 2 + p * u ^ 2 = w ∧ (c < m → c < u) ∧ (m < c → u < c) := by
  have hd : 0 < (m - c) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.2 hne)))
  obtain ⟨D, hD_def⟩ : ∃ D : ℝ, D = (m - c) ^ 2 + (w - m ^ 2) := ⟨_, rfl⟩
  have hD : 0 < D := by
    rw [hD_def]
    exact add_pos_of_pos_of_nonneg hd (sub_nonneg.2 hw)
  obtain ⟨p, hp_def⟩ : ∃ p : ℝ, p = (m - c) ^ 2 / D := ⟨_, rfl⟩
  have hp0 : 0 < p := by
    rw [hp_def]
    exact div_pos hd hD
  have hp1 : p ≤ 1 := by
    rw [hp_def, div_le_one hD, hD_def]
    linarith [sub_nonneg.2 hw]
  have hpD : p * D = (m - c) ^ 2 := by
    have hD_ne : D ≠ 0 := hD.ne'
    rw [hp_def]
    field_simp
  obtain ⟨u, hu_def⟩ : ∃ u : ℝ, u = c + (m - c) / p := ⟨_, rfl⟩
  have hpu : p * (u - c) = m - c := by
    have hp_ne : p ≠ 0 := hp0.ne'
    rw [hu_def, add_sub_cancel_left]
    field_simp
  have hdu : (m - c) * (u - c) = D := by
    refine mul_left_cancel₀ hp0.ne' ?_
    calc p * ((m - c) * (u - c)) = (m - c) * (p * (u - c)) := by ring
      _ = (m - c) ^ 2 := by rw [hpu]; ring
      _ = p * D := hpD.symm
  refine ⟨p, u, hp0, hp1, ?_, ?_, ?_, ?_⟩
  · -- equation (4.3)
    calc (1 - p) * c + p * u = c + p * (u - c) := by ring
      _ = m := by rw [hpu]; ring
  · -- equation (4.4)
    calc (1 - p) * c ^ 2 + p * u ^ 2 = c ^ 2 + p * (u - c) * (u + c) := by ring
      _ = c ^ 2 + (m - c) * (u + c) := by rw [hpu]
      _ = c ^ 2 + 2 * c * (m - c) + (m - c) * (u - c) := by ring
      _ = w := by rw [hdu, hD_def]; ring
  · intro h
    by_contra hcon
    nlinarith [mul_nonneg hp0.le (sub_nonneg.2 (not_lt.1 hcon))]
  · intro h
    by_contra hcon
    nlinarith [mul_nonneg hp0.le (sub_nonneg.2 (not_lt.1 hcon))]

/-- The integral over `A` of a quadratic polynomial, in terms of the first two moments over `A`
and the mass of `A`. -/
private lemma setIntegral_quadratic (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hsq : Integrable (fun x : ℝ => x ^ 2) μ) (hint : Integrable (fun x : ℝ => x) μ)
    (A : Set ℝ) (α β γ : ℝ) :
    ∫ x in A, (α * x ^ 2 + β * x + γ) ∂μ =
      α * (∫ x in A, x ^ 2 ∂μ) + β * (∫ x in A, x ∂μ) + γ * (μ A).toReal := by
  have h1 : Integrable (fun x : ℝ => α * x ^ 2) (μ.restrict A) := hsq.restrict.const_mul α
  have h2 : Integrable (fun x : ℝ => β * x) (μ.restrict A) := hint.restrict.const_mul β
  have h12 : Integrable (fun x : ℝ => α * x ^ 2 + β * x) (μ.restrict A) := h1.add h2
  rw [integral_add h12 (integrable_const γ), integral_add h1 h2, integral_const_mul,
    integral_const_mul, setIntegral_const, smul_eq_mul, measureReal_def]
  ring

/-- If `A` lies strictly above `c` and has positive mass, then `∫_A x > c * μ(A)`; this is
`m > t` in the proof of Martin (2004), Lemma 4.3, without conditioning. -/
private lemma setIntegral_id_gt (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hsq : Integrable (fun x : ℝ => x ^ 2) μ) (hint : Integrable (fun x : ℝ => x) μ)
    {A : Set ℝ} (hA : MeasurableSet A) (hq : μ A ≠ 0) {c : ℝ} (hsub : A ⊆ Ioi c) :
    c * (μ A).toReal < ∫ x in A, x ∂μ := by
  have hnn : 0 ≤ᵐ[μ.restrict A] fun x : ℝ => x - c :=
    ae_restrict_of_forall_mem hA fun x hx => sub_nonneg.2 (le_of_lt (hsub hx))
  have hii : IntegrableOn (fun x : ℝ => x - c) A μ :=
    (hint.sub (integrable_const c)).integrableOn
  have hpos : 0 < ∫ x in A, (x - c) ∂μ := by
    refine (setIntegral_pos_iff_support_of_nonneg_ae hnn hii).2 ?_
    have hsupp : Function.support (fun x : ℝ => x - c) ∩ A = A := by
      ext x
      refine ⟨fun h => h.2, fun hx => ⟨?_, hx⟩⟩
      exact Function.mem_support.2 (sub_pos.2 (hsub hx)).ne'
    rw [hsupp]
    exact pos_iff_ne_zero.2 hq
  have e : (fun x : ℝ => x - c) = fun x => 0 * x ^ 2 + 1 * x + -c := by
    ext x
    ring
  rw [e, setIntegral_quadratic μ hsq hint A 0 1 (-c)] at hpos
  linarith

/-- If `A` lies strictly below `c` and has positive mass, then `∫_A x < c * μ(A)`. -/
private lemma setIntegral_id_lt (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hsq : Integrable (fun x : ℝ => x ^ 2) μ) (hint : Integrable (fun x : ℝ => x) μ)
    {A : Set ℝ} (hA : MeasurableSet A) (hq : μ A ≠ 0) {c : ℝ} (hsub : A ⊆ Iio c) :
    ∫ x in A, x ∂μ < c * (μ A).toReal := by
  have hnn : 0 ≤ᵐ[μ.restrict A] fun x : ℝ => c - x :=
    ae_restrict_of_forall_mem hA fun x hx => sub_nonneg.2 (le_of_lt (hsub hx))
  have hii : IntegrableOn (fun x : ℝ => c - x) A μ :=
    ((integrable_const c).sub hint).integrableOn
  have hpos : 0 < ∫ x in A, (c - x) ∂μ := by
    refine (setIntegral_pos_iff_support_of_nonneg_ae hnn hii).2 ?_
    have hsupp : Function.support (fun x : ℝ => c - x) ∩ A = A := by
      ext x
      refine ⟨fun h => h.2, fun hx => ⟨?_, hx⟩⟩
      exact Function.mem_support.2 (sub_pos.2 (hsub hx)).ne'
    rw [hsupp]
    exact pos_iff_ne_zero.2 hq
  have e : (fun x : ℝ => c - x) = fun x => 0 * x ^ 2 + (-1) * x + c := by
    ext x
    ring
  rw [e, setIntegral_quadratic μ hsq hint A 0 (-1) c] at hpos
  linarith

/-- The conditional second moment over `A` is at least the square of the conditional mean over
`A`: `w >= m^2`, as in the proof of Martin (2004), Lemma 4.3. A conditional variance is
non-negative. -/
private lemma setIntegral_sq_mean_le (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hsq : Integrable (fun x : ℝ => x ^ 2) μ) (hint : Integrable (fun x : ℝ => x) μ)
    {A : Set ℝ} (hA : MeasurableSet A) (hq0 : 0 < (μ A).toReal) :
    ((∫ x in A, x ∂μ) / (μ A).toReal) ^ 2 ≤ (∫ x in A, x ^ 2 ∂μ) / (μ A).toReal := by
  have hqne : (μ A).toReal ≠ 0 := hq0.ne'
  obtain ⟨m, hm_def⟩ : ∃ m : ℝ, m = (∫ x in A, x ∂μ) / (μ A).toReal := ⟨_, rfl⟩
  have hmq : m * (μ A).toReal = ∫ x in A, x ∂μ := by
    rw [hm_def]
    field_simp
  have h3 : m * (∫ x in A, x ∂μ) = m ^ 2 * (μ A).toReal := by
    rw [← hmq]
    ring
  have hnn : 0 ≤ ∫ x in A, (1 * x ^ 2 + (-2 * m) * x + m ^ 2) ∂μ :=
    setIntegral_nonneg hA fun x _ => by nlinarith [sq_nonneg (x - m)]
  rw [setIntegral_quadratic μ hsq hint A 1 (-2 * m) (m ^ 2)] at hnn
  rw [← hm_def, le_div_iff₀ hq0]
  linarith [hnn, h3]

/-- Integrability for the two-point law `κ + α δ_c + β δ_u`. -/
private lemma integrable_two_point {κ : Measure ℝ} {f : ℝ → ℝ} (hf : Integrable f κ)
    (α β c u : ℝ) :
    Integrable f (κ + ENNReal.ofReal α • Measure.dirac c + ENNReal.ofReal β • Measure.dirac u) :=
  (hf.add_measure ((integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top)).add_measure
    ((integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top)

/-- The integral for the two-point law `κ + α δ_c + β δ_u`, with `α, β ≥ 0`. -/
private lemma integral_two_point {κ : Measure ℝ} {f : ℝ → ℝ} (hf : Integrable f κ)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (c u : ℝ) :
    ∫ x, f x ∂(κ + ENNReal.ofReal α • Measure.dirac c + ENNReal.ofReal β • Measure.dirac u) =
      ∫ x, f x ∂κ + α * f c + β * f u := by
  have hdc : Integrable f (ENNReal.ofReal α • Measure.dirac c) :=
    (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top
  have hdu : Integrable f (ENNReal.ofReal β • Measure.dirac u) :=
    (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top
  rw [integral_add_measure (hf.add_measure hdc) hdu, integral_add_measure hf hdc,
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac,
    ENNReal.toReal_ofReal hα, ENNReal.toReal_ofReal hβ, smul_eq_mul, smul_eq_mul]

/-- The mass that the two-point law `κ + α δ_c + β δ_u` gives to a measurable set. -/
theorem martin_two_point_apply (κ : Measure ℝ) (α β : ℝ≥0∞) (c u : ℝ) {S : Set ℝ}
    (hS : MeasurableSet S) :
    (κ + α • Measure.dirac c + β • Measure.dirac u) S =
      κ S + α * Set.indicator S (1 : ℝ → ℝ≥0∞) c + β * Set.indicator S (1 : ℝ → ℝ≥0∞) u := by
  rw [Measure.add_apply, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply' _ hS, Measure.dirac_apply' _ hS, smul_eq_mul, smul_eq_mul]

/-! ### The two-point replacement (equations (4.3) to (4.5)) -/

/-- **Two-point replacement** (Martin (2004), Lemma 4.3: the solution of (4.3) and (4.4) and
the mass formula (4.5)), for the mass on a measurable set `A` of positive measure that lies on one
side of `c`. With `q = μ A`, there are weights `(1 - p) q` at `c` and `p q` at a point `u` on the
same side of `c` as `A`, with `0 < p ≤ 1`, such that the law `ν` obtained by removing the mass on
`A` and adding these two atoms is a probability measure with a finite second moment, the same
mean and the same second moment as `μ`, and `p q u ^ 2` is at most the second moment of `μ`
over `A`. -/
theorem martin_two_point_replacement
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hsq : Integrable (fun x : ℝ => x ^ 2) μ)
    {A : Set ℝ} (hA : MeasurableSet A) (hq : μ A ≠ 0) {c : ℝ}
    (hc : A ⊆ Ioi c ∨ A ⊆ Iio c) :
    ∃ p u : ℝ, 0 < p ∧ p ≤ 1 ∧ (A ⊆ Ioi c → c < u) ∧ (A ⊆ Iio c → u < c) ∧
      p * (μ A).toReal * u ^ 2 ≤ ∫ x in A, x ^ 2 ∂μ ∧
      ∃ ν : Measure ℝ,
        ν = μ.restrict Aᶜ + ENNReal.ofReal ((1 - p) * (μ A).toReal) • Measure.dirac c +
          ENNReal.ofReal (p * (μ A).toReal) • Measure.dirac u ∧
        IsProbabilityMeasure ν ∧ Integrable (fun x : ℝ => x ^ 2) ν ∧
        ∫ x, x ∂ν = ∫ x, x ∂μ ∧ ∫ x, x ^ 2 ∂ν = ∫ x, x ^ 2 ∂μ := by
  have hint : Integrable (fun x : ℝ => x) μ := integrable_id_of_integrable_sq μ hsq
  have hqfin : μ A ≠ ∞ := measure_ne_top μ A
  have hq0 : 0 < (μ A).toReal := ENNReal.toReal_pos hq hqfin
  have hqne : (μ A).toReal ≠ 0 := hq0.ne'
  -- the conditional mean `m` and second moment `w` over `A`, and the side of `c` they lie on
  have hm_pos : A ⊆ Ioi c → c < (∫ x in A, x ∂μ) / (μ A).toReal := fun hsub => by
    rw [lt_div_iff₀ hq0]
    exact setIntegral_id_gt μ hsq hint hA hq hsub
  have hm_neg : A ⊆ Iio c → (∫ x in A, x ∂μ) / (μ A).toReal < c := fun hsub => by
    rw [div_lt_iff₀ hq0]
    exact setIntegral_id_lt μ hsq hint hA hq hsub
  have hne : (∫ x in A, x ∂μ) / (μ A).toReal ≠ c := by
    rcases hc with h | h
    · exact (hm_pos h).ne'
    · exact (hm_neg h).ne
  -- the solution `p`, `u` of (4.3) and (4.4)
  obtain ⟨p, u, hp0, hp1, h43, h44, hup, hdown⟩ :=
    exists_two_point_parameters hne (setIntegral_sq_mean_le μ hsq hint hA hq0)
  have hα : 0 ≤ (1 - p) * (μ A).toReal := mul_nonneg (sub_nonneg.2 hp1) hq0.le
  have hβ : 0 ≤ p * (μ A).toReal := mul_nonneg hp0.le hq0.le
  -- the two weighted equations: mass times (4.3) and mass times (4.4)
  have key1 : (1 - p) * (μ A).toReal * c + p * (μ A).toReal * u = ∫ x in A, x ∂μ := by
    have e : (1 - p) * (μ A).toReal * c + p * (μ A).toReal * u =
        (μ A).toReal * ((1 - p) * c + p * u) := by ring
    rw [e, h43]
    field_simp
  have key2 : (1 - p) * (μ A).toReal * c ^ 2 + p * (μ A).toReal * u ^ 2 =
      ∫ x in A, x ^ 2 ∂μ := by
    have e : (1 - p) * (μ A).toReal * c ^ 2 + p * (μ A).toReal * u ^ 2 =
        (μ A).toReal * ((1 - p) * c ^ 2 + p * u ^ 2) := by ring
    rw [e, h44]
    field_simp
  -- `p q u ^ 2 ≤ ∫_A x ^ 2`, as the term `(1 - p) q c ^ 2` is non-negative
  have hbound : p * (μ A).toReal * u ^ 2 ≤ ∫ x in A, x ^ 2 ∂μ := by
    nlinarith [mul_nonneg hα (sq_nonneg c)]
  obtain ⟨ν, hν⟩ : ∃ ν : Measure ℝ,
      ν = μ.restrict Aᶜ + ENNReal.ofReal ((1 - p) * (μ A).toReal) • Measure.dirac c +
        ENNReal.ofReal (p * (μ A).toReal) • Measure.dirac u := ⟨_, rfl⟩
  -- total mass one
  have hmass : ν univ = 1 := by
    rw [hν, martin_two_point_apply _ _ _ _ _ MeasurableSet.univ]
    simp only [Measure.restrict_apply_univ, indicator_univ, Pi.one_apply, mul_one]
    rw [add_assoc, ← ENNReal.ofReal_add hα hβ,
      show (1 - p) * (μ A).toReal + p * (μ A).toReal = (μ A).toReal by ring,
      ENNReal.ofReal_toReal hqfin, add_comm, measure_add_measure_compl hA, measure_univ]
  refine ⟨p, u, hp0, hp1, fun h => hup (hm_pos h), fun h => hdown (hm_neg h), hbound,
    ν, hν, ⟨hmass⟩, ?_, ?_, ?_⟩
  · rw [hν]
    exact integrable_two_point hsq.restrict _ _ c u
  · -- the mean is kept, by (4.3)
    rw [hν, integral_two_point hint.restrict hα hβ c u, ← integral_add_compl hA hint]
    linarith [key1]
  · -- the second moment is kept, by (4.4)
    rw [hν, integral_two_point hsq.restrict hα hβ c u, ← integral_add_compl hA hsq]
    linarith [key2]

/-! ### Square-root bounds for distribution functions -/

/-- If `|x|` is at most the sum of two finite masses (as real numbers), then the square root of
`|x|` is at most the sum of the square roots of the masses, as extended non-negative reals. -/
private lemma ofReal_abs_rpow_le_add {x : ℝ} {a b : ℝ≥0∞} (ha : a ≠ ∞) (hb : b ≠ ∞)
    (h : |x| ≤ a.toReal + b.toReal) :
    ENNReal.ofReal (|x| ^ (1 / 2 : ℝ)) ≤ a ^ (1 / 2 : ℝ) + b ^ (1 / 2 : ℝ) := by
  rw [← ENNReal.ofReal_rpow_of_nonneg (abs_nonneg x) (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  calc ENNReal.ofReal |x| ^ (1 / 2 : ℝ) ≤ (a + b) ^ (1 / 2 : ℝ) := by
        refine ENNReal.rpow_le_rpow ?_ (by norm_num)
        calc ENNReal.ofReal |x| ≤ ENNReal.ofReal (a.toReal + b.toReal) :=
              ENNReal.ofReal_le_ofReal h
          _ = a + b := by
              rw [ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
                ENNReal.ofReal_toReal ha, ENNReal.ofReal_toReal hb]
    _ ≤ a ^ (1 / 2 : ℝ) + b ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_add_le_add_rpow _ _ (by norm_num) (by norm_num)

/-- For a probability measure, `F s` and the upper tail at `s` add to one. -/
private lemma toReal_Iic_add_Ioi (μ : Measure ℝ) [IsProbabilityMeasure μ] (s : ℝ) :
    (μ (Iic s)).toReal + (μ (Ioi s)).toReal = 1 := by
  have h := measure_add_measure_compl (μ := μ) (measurableSet_Iic (a := s))
  rw [compl_Iic, measure_univ] at h
  have h' := congrArg ENNReal.toReal h
  rwa [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), ENNReal.toReal_one] at h'

/-- A step in the proof of Martin (2004), Lemma 4.3: the square root of the difference of two
distribution functions is at most the sum of the square roots of the two upper tails, since
the square root of a sum is at most the sum of the square roots. -/
theorem martin_sqrt_cdf_dist_le_upper (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (s : ℝ) :
    ENNReal.ofReal (|(μ (Iic s)).toReal - (ν (Iic s)).toReal| ^ (1 / 2 : ℝ)) ≤
      (μ (Ioi s)) ^ (1 / 2 : ℝ) + (ν (Ioi s)) ^ (1 / 2 : ℝ) := by
  have hμ := toReal_Iic_add_Ioi μ s
  have hν := toReal_Iic_add_Ioi ν s
  refine ofReal_abs_rpow_le_add (measure_ne_top _ _) (measure_ne_top _ _) ?_
  rw [abs_le]
  constructor <;>
    linarith [ENNReal.toReal_nonneg (a := μ (Ioi s)), ENNReal.toReal_nonneg (a := ν (Ioi s))]

/-- The mirror of `martin_sqrt_cdf_dist_le_upper` for the lower tails, used for the negative
tail: the square root of the difference of two distribution functions is at most the sum of the
square roots of the two lower tails. -/
theorem martin_sqrt_cdf_dist_le_lower (μ ν : Measure ℝ) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (s : ℝ) :
    ENNReal.ofReal (|(μ (Iic s)).toReal - (ν (Iic s)).toReal| ^ (1 / 2 : ℝ)) ≤
      (μ (Iic s)) ^ (1 / 2 : ℝ) + (ν (Iic s)) ^ (1 / 2 : ℝ) := by
  refine ofReal_abs_rpow_le_add (measure_ne_top _ _) (measure_ne_top _ _) ?_
  rw [abs_le]
  constructor <;>
    linarith [ENNReal.toReal_nonneg (a := μ (Iic s)), ENNReal.toReal_nonneg (a := ν (Iic s))]

/-- The final estimate in the proof of Martin (2004), Lemma 4.3: the middle atom costs at most
`E (X ^ 2; X > t) ^ (1/2)`. With `r = p q`
and a point `u` such that `r u ^ 2` is at most the second moment of `μ` over `A`, a step of width
`d ≤ |u|` of height `r ^ (1/2)` has area at most the square root of that second moment. -/
theorem martin_atom_sqrt_le (μ : Measure ℝ) (hsq : Integrable (fun x : ℝ => x ^ 2) μ)
    {A : Set ℝ} {r u d : ℝ} (hr : 0 ≤ r) (hru : r * u ^ 2 ≤ ∫ x in A, x ^ 2 ∂μ)
    (hd : d ≤ |u|) :
    ENNReal.ofReal r ^ (1 / 2 : ℝ) * ENNReal.ofReal d ≤
      (∫⁻ x in A, ENNReal.ofReal (x ^ 2) ∂μ) ^ (1 / 2 : ℝ) := by
  have hI : ENNReal.ofReal (∫ x in A, x ^ 2 ∂μ) = ∫⁻ x in A, ENNReal.ofReal (x ^ 2) ∂μ :=
    ofReal_integral_eq_lintegral_ofReal hsq.restrict (Eventually.of_forall fun x => sq_nonneg x)
  have hreal : r ^ (1 / 2 : ℝ) * d ≤ (r * u ^ 2) ^ (1 / 2 : ℝ) := by
    rw [Real.mul_rpow hr (sq_nonneg u), ← Real.sqrt_eq_rpow (u ^ 2), Real.sqrt_sq_eq_abs]
    exact mul_le_mul_of_nonneg_left hd (Real.rpow_nonneg hr _)
  calc ENNReal.ofReal r ^ (1 / 2 : ℝ) * ENNReal.ofReal d
      = ENNReal.ofReal (r ^ (1 / 2 : ℝ) * d) := by
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg hr _),
          ENNReal.ofReal_rpow_of_nonneg hr (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    _ ≤ ENNReal.ofReal ((r * u ^ 2) ^ (1 / 2 : ℝ)) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (r * u ^ 2) ^ (1 / 2 : ℝ) :=
        (ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hr (sq_nonneg u))
          (by norm_num : (0 : ℝ) ≤ 1 / 2)).symm
    _ ≤ ENNReal.ofReal (∫ x in A, x ^ 2 ∂μ) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hru) (by norm_num)
    _ = (∫⁻ x in A, ENNReal.ofReal (x ^ 2) ∂μ) ^ (1 / 2 : ℝ) := by rw [hI]

/-! ### The upper tail -/

/-- **Lemma 4.3, upper tail** (Martin (2004), with the whole line in place of `X ≥ 0`).
For a probability measure `μ` with finite second moment and a level `t ≥ 0`, replacing the mass
above `t` by two atoms gives a probability measure `ν` that is bounded above, equal to `μ` below
`t`, has the same mean and second moment, and whose square-root distance from `μ` is at most the
integral of the square root of the upper tail above `t` plus the square root of
`E (X ^ 2; X > t)`. -/
theorem martin_truncation_upper_tail
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hsq : Integrable (fun x : ℝ => x ^ 2) μ)
    {t : ℝ} (ht : 0 ≤ t) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ (∃ L : ℝ, ∀ᵐ x ∂ν, x ≤ L) ∧
      ν.restrict (Iio t) = μ.restrict (Iio t) ∧
      Integrable (fun x : ℝ => x ^ 2) ν ∧
      ∫ x, x ∂ν = ∫ x, x ∂μ ∧ ∫ x, x ^ 2 ∂ν = ∫ x, x ^ 2 ∂μ ∧
      (∫⁻ s : ℝ, ENNReal.ofReal
          (|(μ (Iic s)).toReal - (ν (Iic s)).toReal| ^ (1 / 2 : ℝ))) ≤
        (∫⁻ s in Ioi t, (μ (Ioi s)) ^ (1 / 2 : ℝ)) +
          (∫⁻ x in Ioi t, ENNReal.ofReal (x ^ 2) ∂μ) ^ (1 / 2 : ℝ) := by
  by_cases hP : μ (Ioi t) = 0
  · -- if `P (X > t) = 0` the law already has bounded support (start of the proof of Lemma 4.3)
    refine ⟨μ, inferInstance, ⟨t, ?_⟩, rfl, hsq, rfl, rfl, ?_⟩
    · exact (measure_eq_zero_iff_ae_notMem.1 hP).mono fun x hx => not_lt.1 hx
    · have hzero : ∀ s : ℝ, ENNReal.ofReal
          (|(μ (Iic s)).toReal - (μ (Iic s)).toReal| ^ (1 / 2 : ℝ)) = 0 := fun s => by
        rw [sub_self, abs_zero, Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0),
          ENNReal.ofReal_zero]
      rw [lintegral_congr hzero, lintegral_zero]
      exact zero_le
  · obtain ⟨p, u, hp0, hp1, hup, -, hpu, ν, hν, hprob, hsqν, hmean, hsecond⟩ :=
      martin_two_point_replacement μ hsq measurableSet_Ioi hP (c := t) (Or.inl subset_rfl)
    have hu : t < u := hup subset_rfl
    have hq0 : 0 < (μ (Ioi t)).toReal := ENNReal.toReal_pos hP (measure_ne_top _ _)
    have hν' : ν = μ.restrict (Iic t) +
        ENNReal.ofReal ((1 - p) * (μ (Ioi t)).toReal) • Measure.dirac t +
          ENNReal.ofReal (p * (μ (Ioi t)).toReal) • Measure.dirac u := by
      rw [hν, compl_Ioi]
    -- (4.5), below `t` the distribution functions agree
    have hcdf : ∀ s : ℝ, s < t → ν (Iic s) = μ (Iic s) := by
      intro s hs
      have hts : t ∉ Iic s := fun h => (not_le.2 hs) (mem_Iic.1 h)
      have hus : u ∉ Iic s := fun h => (not_le.2 (hs.trans hu)) (mem_Iic.1 h)
      rw [hν', martin_two_point_apply _ _ _ _ _ measurableSet_Iic,
        Measure.restrict_apply measurableSet_Iic, inter_eq_left.2 (Iic_subset_Iic.2 hs.le),
        indicator_of_notMem hts, indicator_of_notMem hus]
      simp
    -- (4.5), above `t` the upper tail of `ν` is `p q` up to `u` and `0` after
    have htail : ∀ s : ℝ, t ≤ s → ν (Ioi s) =
        ENNReal.ofReal (p * (μ (Ioi t)).toReal) * Set.indicator (Ioi s) (1 : ℝ → ℝ≥0∞) u := by
      intro s hs
      have hts : t ∉ Ioi s := fun h => (not_lt.2 hs) (mem_Ioi.1 h)
      rw [hν', martin_two_point_apply _ _ _ _ _ measurableSet_Ioi,
        Measure.restrict_apply measurableSet_Ioi, Ioi_inter_Iic, Ioc_eq_empty_of_le hs,
        measure_empty, indicator_of_notMem hts]
      simp
    -- `ν` is bounded above by `u`: `F~ (u) = 1`
    have hbdd : ∀ᵐ x ∂ν, x ≤ u := by
      have h0 : ν (Ioi u) = 0 := by
        rw [htail u hu.le]
        simp
      exact (measure_eq_zero_iff_ae_notMem.1 h0).mono fun x hx => not_lt.1 hx
    -- `ν` and `μ` agree below `t`
    have hagree : ν.restrict (Iio t) = μ.restrict (Iio t) := by
      refine Measure.ext fun S hS => ?_
      have hS' : MeasurableSet (S ∩ Iio t) := hS.inter measurableSet_Iio
      have htn : t ∉ S ∩ Iio t := fun h => lt_irrefl t (mem_Iio.1 h.2)
      have hun : u ∉ S ∩ Iio t := fun h => (not_lt.2 hu.le) (mem_Iio.1 h.2)
      rw [Measure.restrict_apply hS, Measure.restrict_apply hS, hν',
        martin_two_point_apply _ _ _ _ _ hS', Measure.restrict_apply hS',
        indicator_of_notMem htn, indicator_of_notMem hun, mul_zero, mul_zero, add_zero, add_zero,
        inter_eq_left.2 (inter_subset_right.trans Iio_subset_Iic_self)]
    refine ⟨ν, hprob, ⟨u, hbdd⟩, hagree, hsqν, hmean, hsecond, ?_⟩
    -- the distance estimate at the end of the proof of Martin (2004), Lemma 4.3
    have hmeas : Measurable fun s : ℝ => μ (Ioi s) ^ (1 / 2 : ℝ) :=
      Antitone.measurable fun _ _ hst =>
        ENNReal.rpow_le_rpow (measure_mono (Ioi_subset_Ioi hst)) (by norm_num)
    have hpt : ∀ s : ℝ, ENNReal.ofReal
        (|(μ (Iic s)).toReal - (ν (Iic s)).toReal| ^ (1 / 2 : ℝ)) ≤
        (Ici t).indicator (fun s => μ (Ioi s) ^ (1 / 2 : ℝ) + ν (Ioi s) ^ (1 / 2 : ℝ)) s := by
      intro s
      by_cases hs : s < t
      · have hzero : ENNReal.ofReal
            (|(μ (Iic s)).toReal - (ν (Iic s)).toReal| ^ (1 / 2 : ℝ)) = 0 := by
          rw [hcdf s hs, sub_self, abs_zero, Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0),
            ENNReal.ofReal_zero]
        rw [hzero]
        exact zero_le
      · rw [indicator_of_mem (mem_Ici.2 (not_lt.1 hs))]
        exact martin_sqrt_cdf_dist_le_upper μ ν s
    have hIci : ∀ f : ℝ → ℝ≥0∞, ∫⁻ s in Ici t, f s = ∫⁻ s in Ioi t, f s :=
      fun f => setLIntegral_congr Ioi_ae_eq_Ici.symm
    -- the integral of the square root of the tail of `ν` over `(t, u)`
    have hatom : ∫⁻ s in Ioi t, ν (Ioi s) ^ (1 / 2 : ℝ) =
        ENNReal.ofReal (p * (μ (Ioi t)).toReal) ^ (1 / 2 : ℝ) * ENNReal.ofReal (u - t) := by
      have hcongr : ∫⁻ s in Ioi t, ν (Ioi s) ^ (1 / 2 : ℝ) =
          ∫⁻ s in Ioi t, (Iio u).indicator
            (fun _ : ℝ => ENNReal.ofReal (p * (μ (Ioi t)).toReal) ^ (1 / 2 : ℝ)) s := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
        rw [htail s (mem_Ioi.1 hs).le]
        by_cases hsu : s < u
        · rw [indicator_of_mem (show u ∈ Ioi s from hsu),
            indicator_of_mem (show s ∈ Iio u from hsu), Pi.one_apply, mul_one]
        · rw [indicator_of_notMem (show u ∉ Ioi s from fun h => hsu (mem_Ioi.1 h)),
            indicator_of_notMem (show s ∉ Iio u from fun h => hsu (mem_Iio.1 h)), mul_zero,
            ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      rw [hcongr, lintegral_indicator measurableSet_Iio, setLIntegral_const,
        Measure.restrict_apply measurableSet_Iio, Iio_inter_Ioi, Real.volume_Ioo]
    have hd : u - t ≤ |u| := by
      have := le_abs_self u
      linarith
    calc ∫⁻ s : ℝ, ENNReal.ofReal (|(μ (Iic s)).toReal - (ν (Iic s)).toReal| ^ (1 / 2 : ℝ))
        ≤ ∫⁻ s : ℝ, (Ici t).indicator
            (fun s => μ (Ioi s) ^ (1 / 2 : ℝ) + ν (Ioi s) ^ (1 / 2 : ℝ)) s := lintegral_mono hpt
      _ = ∫⁻ s in Ici t, (μ (Ioi s) ^ (1 / 2 : ℝ) + ν (Ioi s) ^ (1 / 2 : ℝ)) :=
          lintegral_indicator measurableSet_Ici _
      _ = (∫⁻ s in Ici t, μ (Ioi s) ^ (1 / 2 : ℝ)) +
            ∫⁻ s in Ici t, ν (Ioi s) ^ (1 / 2 : ℝ) := lintegral_add_left hmeas _
      _ = (∫⁻ s in Ioi t, μ (Ioi s) ^ (1 / 2 : ℝ)) +
            ∫⁻ s in Ioi t, ν (Ioi s) ^ (1 / 2 : ℝ) := by rw [hIci, hIci]
      _ ≤ (∫⁻ s in Ioi t, μ (Ioi s) ^ (1 / 2 : ℝ)) +
            (∫⁻ x in Ioi t, ENNReal.ofReal (x ^ 2) ∂μ) ^ (1 / 2 : ℝ) := by
          rw [hatom]
          exact add_le_add le_rfl
            (martin_atom_sqrt_le μ hsq (mul_nonneg hp0.le hq0.le) hpu hd)

end LPPDifferentiability

end
