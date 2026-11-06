/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.KLFun
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Entropy of positive bounded functions

The entropy functional used in the entropy method for concentration inequalities. The
mathematics follows Boucheron, Lugosi and Massart (2013), Chapter 4, with every step written out.
This is general probability and does not depend on the LPP model.

## Main definitions

* `entropy μ g`: `∫ g log g ∂μ - (∫ g ∂μ) log (∫ g ∂μ)`, with the unfolding lemma `entropy_eq`.

## Main results

Throughout, `μ` and `ν` are probability measures and the functions are measurable with values in
a bounded interval `[a, b]` with `0 < a`, so that every integral involved is of a bounded
measurable function.

* `entropy_le_integral_of_pos`: for `u > 0`, `Ent(g) ≤ E[g log g - g log u - g + u]`.
* `integral_mul_le_entropy` (Gibbs): if `E e^h = 1` then `E[g h] ≤ Ent(g)`.
* `entropy_prod_eq` (chain rule): on a product measure, `Ent(g)` is the average of the entropy in
  the first coordinate plus the entropy of the average.
* `entropy_integral_le` (convexity): averaging over one coordinate before taking the entropy in the
  other does not increase it.

## Proof outline

The variational bound and Gibbs' inequality both come from `InformationTheory.klFun_nonneg`. The
chain rule is Fubini's theorem applied to `g log g` and `g`. Convexity combines Fubini with Gibbs'
inequality for the test function `h = log (G / E G)`.

## References

- S. Boucheron, G. Lugosi and P. Massart, *Concentration Inequalities: A Nonasymptotic Theory of
  Independence*, Oxford University Press, 2013, Chapter 4.
-/

@[expose] public section

open MeasureTheory Set

namespace ProbabilityBasics.Concentration

/-- The entropy of a real function `g` under the measure `μ`:
`∫ g log g ∂μ - (∫ g ∂μ) log (∫ g ∂μ)`. It is used for positive bounded measurable functions
and probability measures. Boucheron, Lugosi and Massart (2013), Chapter 4 (notation `Ent`). -/
noncomputable def entropy {α : Type*} [MeasurableSpace α] (μ : Measure α) (g : α → ℝ) : ℝ :=
  (∫ x, g x * Real.log (g x) ∂μ) - (∫ x, g x ∂μ) * Real.log (∫ x, g x ∂μ)

/-- Unfolding lemma for `entropy`. -/
theorem entropy_eq {α : Type*} [MeasurableSpace α] (μ : Measure α) (g : α → ℝ) :
    entropy μ g =
      (∫ x, g x * Real.log (g x) ∂μ) - (∫ x, g x ∂μ) * Real.log (∫ x, g x ∂μ) := rfl

section Entropy

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-! ### Bounds on functions with values in `[a, b]` -/

/-- A value in `[a, b]` has absolute value at most `|a| + |b|`. -/
lemma abs_le_of_mem_Icc {a b t : ℝ} (ht : t ∈ Icc a b) : |t| ≤ |a| + |b| :=
  abs_le.2 ⟨by linarith [neg_abs_le a, ht.1, abs_nonneg b],
    by linarith [le_abs_self b, ht.2, abs_nonneg a]⟩

/-- The logarithm of a value in `[a, b]`, `0 < a`, has absolute value at most
`|log a| + |log b|`. -/
lemma abs_log_le_of_mem_Icc {a b t : ℝ} (ha : 0 < a) (ht : t ∈ Icc a b) :
    |Real.log t| ≤ |Real.log a| + |Real.log b| := by
  have hlog_lower : Real.log a ≤ Real.log t := Real.log_le_log ha ht.1
  have hlog_upper : Real.log t ≤ Real.log b := Real.log_le_log (ha.trans_le ht.1) ht.2
  exact abs_le_of_mem_Icc ⟨hlog_lower, hlog_upper⟩

/-- If `t ∈ [a, b]` with `0 < a` and `|s| ≤ M`, then `|t s| ≤ b M`. -/
lemma abs_mul_le_of_mem_Icc {a b t s M : ℝ} (ha : 0 < a) (ht : t ∈ Icc a b)
    (hs : |s| ≤ M) : |t * s| ≤ b * M := by
  have ht_pos : 0 < t := ha.trans_le ht.1
  rw [abs_mul, abs_of_pos ht_pos]
  exact mul_le_mul ht.2 hs (abs_nonneg _) (ht_pos.le.trans ht.2)

/-- A measurable function that is bounded in absolute value is integrable for a probability
measure. -/
lemma integrable_of_abs_le (μ : Measure α) [IsProbabilityMeasure μ] {f : α → ℝ} {M : ℝ}
    (hf : Measurable f) (hfM : ∀ x, |f x| ≤ M) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable M
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hfM x)

/-- The mean of a measurable function with values in `[a, b]` lies in `[a, b]`. -/
lemma integral_mem_Icc (μ : Measure α) [IsProbabilityMeasure μ] {g : α → ℝ} {a b : ℝ}
    (hg : Measurable g) (hgab : ∀ x, g x ∈ Icc a b) : ∫ x, g x ∂μ ∈ Icc a b := by
  have hg_int : Integrable g μ := integrable_of_abs_le μ hg fun x => abs_le_of_mem_Icc (hgab x)
  constructor
  · have hlower := integral_mono (integrable_const a) hg_int fun x => (hgab x).1
    simpa using hlower
  · have hupper := integral_mono hg_int (integrable_const b) fun x => (hgab x).2
    simpa using hupper

/-- `g log g` is integrable when `g` is measurable with values in `[a, b]`, `0 < a`. -/
private lemma integrable_mul_log (μ : Measure α) [IsProbabilityMeasure μ] {g : α → ℝ}
    {a b : ℝ} (ha : 0 < a) (hg : Measurable g) (hgab : ∀ x, g x ∈ Icc a b) :
    Integrable (fun x => g x * Real.log (g x)) μ :=
  integrable_of_abs_le μ (hg.mul hg.log) fun x =>
    abs_mul_le_of_mem_Icc ha (hgab x) (abs_log_le_of_mem_Icc ha (hgab x))

/-! ### The variational bound -/

/-- Variational bound with a constant: `Ent(g) ≤ E[g log g - g log u - g + u]` for every `u > 0`.
The difference of the two sides is `u · klFun (E g / u) ≥ 0`.
Source: Boucheron, Lugosi and Massart (2013), Chapter 4 (variational formulas for entropy). -/
theorem entropy_le_integral_of_pos (μ : Measure α) [IsProbabilityMeasure μ]
    {g : α → ℝ} {a b : ℝ} (ha : 0 < a) (hg : Measurable g) (hgab : ∀ x, g x ∈ Icc a b)
    {u : ℝ} (hu : 0 < u) :
    entropy μ g ≤ ∫ x, (g x * Real.log (g x) - g x * Real.log u - g x + u) ∂μ := by
  have hg_int : Integrable g μ := integrable_of_abs_le μ hg fun x => abs_le_of_mem_Icc (hgab x)
  have hgl_int := integrable_mul_log μ ha hg hgab
  have hm_mem := integral_mem_Icc μ hg hgab
  have hm_pos : 0 < ∫ x, g x ∂μ := ha.trans_le hm_mem.1
  obtain ⟨m, hm⟩ : ∃ m, ∫ x, g x ∂μ = m := ⟨_, rfl⟩
  rw [hm] at hm_pos
  have hkl_nonneg : 0 ≤ u * InformationTheory.klFun (m / u) :=
    mul_nonneg hu.le (InformationTheory.klFun_nonneg (div_nonneg hm_pos.le hu.le))
  have hkl_eq : u * InformationTheory.klFun (m / u) =
      m * Real.log m - m * Real.log u - m + u := by
    rw [InformationTheory.klFun_apply, Real.log_div hm_pos.ne' hu.ne']
    field_simp
    ring
  have hrhs : ∫ x, (g x * Real.log (g x) - g x * Real.log u - g x + u) ∂μ =
      (∫ x, g x * Real.log (g x) ∂μ) - m * Real.log u - m + u := by
    have hdiff_int : Integrable (fun x => g x * Real.log (g x) - g x * Real.log u) μ :=
      hgl_int.sub (hg_int.mul_const _)
    have hdiff2_int :
        Integrable (fun x => g x * Real.log (g x) - g x * Real.log u - g x) μ :=
      hdiff_int.sub hg_int
    rw [integral_add hdiff2_int (integrable_const u), integral_sub hdiff_int hg_int,
      integral_sub hgl_int (hg_int.mul_const _), integral_mul_const, hm]
    simp
  rw [entropy_eq, hm, hrhs]
  linarith

/-! ### Gibbs' inequality -/

/-- Young's inequality in the form used for Gibbs' inequality: for `p, m > 0` and real `y`,
`p y ≤ p log p - p log m - p + m e^y`. It is `m e^y · klFun (p e^{-y} / m) ≥ 0`. -/
private lemma mul_le_mul_log_sub_add_exp {p m y : ℝ} (hp : 0 < p) (hm : 0 < m) :
    p * y ≤ p * Real.log p - p * Real.log m - p + m * Real.exp y := by
  have hq_nonneg : 0 ≤ InformationTheory.klFun (p * Real.exp (-y) / m) :=
    InformationTheory.klFun_nonneg (by positivity)
  have hlog : Real.log (p * Real.exp (-y) / m) = Real.log p - y - Real.log m := by
    rw [Real.log_div (by positivity) hm.ne', Real.log_mul hp.ne' (Real.exp_pos _).ne',
      Real.log_exp]
    ring
  have hscaled : 0 ≤ m * Real.exp y * InformationTheory.klFun (p * Real.exp (-y) / m) :=
    mul_nonneg (by positivity) hq_nonneg
  have hexp_ne : Real.exp y ≠ 0 := (Real.exp_pos y).ne'
  have hscaled_eq : m * Real.exp y * InformationTheory.klFun (p * Real.exp (-y) / m) =
      p * Real.log p - p * y - p * Real.log m - p + m * Real.exp y := by
    rw [InformationTheory.klFun_apply, hlog, Real.exp_neg]
    field_simp
    ring
  linarith

/-- Duality (Gibbs) bound: if `E e^h = 1` then `E[g h] ≤ Ent(g)`. Apply Young's inequality with
`p = g x`, `m = E g` and integrate.
Source: Boucheron, Lugosi and Massart (2013), Chapter 4 (duality formula for entropy). -/
theorem integral_mul_le_entropy (μ : Measure α) [IsProbabilityMeasure μ]
    {g h : α → ℝ} {a b M : ℝ} (ha : 0 < a) (hg : Measurable g) (hgab : ∀ x, g x ∈ Icc a b)
    (hh : Measurable h) (hhM : ∀ x, |h x| ≤ M) (hexp : ∫ x, Real.exp (h x) ∂μ = 1) :
    ∫ x, g x * h x ∂μ ≤ entropy μ g := by
  have hg_int : Integrable g μ := integrable_of_abs_le μ hg fun x => abs_le_of_mem_Icc (hgab x)
  have hgl_int := integrable_mul_log μ ha hg hgab
  have hm_mem := integral_mem_Icc μ hg hgab
  have hm_pos : 0 < ∫ x, g x ∂μ := ha.trans_le hm_mem.1
  have hgh_int : Integrable (fun x => g x * h x) μ :=
    integrable_of_abs_le μ (hg.mul hh) fun x => abs_mul_le_of_mem_Icc ha (hgab x) (hhM x)
  have hexp_int : Integrable (fun x => Real.exp (h x)) μ := by
    refine integrable_of_abs_le μ hh.exp (M := Real.exp M) fun x => ?_
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 ((le_abs_self _).trans (hhM x))
  obtain ⟨m, hm⟩ : ∃ m, ∫ x, g x ∂μ = m := ⟨_, rfl⟩
  rw [hm] at hm_pos
  have hdiff_int : Integrable (fun x => g x * Real.log (g x) - g x * Real.log m) μ :=
    hgl_int.sub (hg_int.mul_const _)
  have hdiff2_int : Integrable (fun x => g x * Real.log (g x) - g x * Real.log m - g x) μ :=
    hdiff_int.sub hg_int
  have hbound_int : Integrable
      (fun x => g x * Real.log (g x) - g x * Real.log m - g x + m * Real.exp (h x)) μ :=
    hdiff2_int.add (hexp_int.const_mul m)
  have hpoint : ∀ x, g x * h x ≤
      g x * Real.log (g x) - g x * Real.log m - g x + m * Real.exp (h x) := fun x =>
    mul_le_mul_log_sub_add_exp (ha.trans_le (hgab x).1) hm_pos
  have hmono := integral_mono hgh_int hbound_int hpoint
  have hrhs : ∫ x, (g x * Real.log (g x) - g x * Real.log m - g x + m * Real.exp (h x)) ∂μ =
      (∫ x, g x * Real.log (g x) ∂μ) - m * Real.log m - m + m * 1 := by
    rw [integral_add hdiff2_int (hexp_int.const_mul m), integral_sub hdiff_int hg_int,
      integral_sub hgl_int (hg_int.mul_const _), integral_mul_const, integral_const_mul, hexp,
      hm]
  rw [hrhs] at hmono
  rw [entropy_eq, hm]
  linarith

/-! ### Sections of a function on a product -/

/-- Integrating out the first coordinate of a measurable function gives a measurable function of
the second coordinate. -/
private lemma measurable_integral_left (μ : Measure α) [IsProbabilityMeasure μ]
    {g : α × β → ℝ} (hg : Measurable g) : Measurable fun y => ∫ x, g (x, y) ∂μ :=
  hg.stronglyMeasurable.integral_prod_left'.measurable

/-- Integrating out the second coordinate of a measurable function gives a measurable function of
the first coordinate. -/
private lemma measurable_integral_right (ν : Measure β) [IsProbabilityMeasure ν]
    {g : α × β → ℝ} (hg : Measurable g) : Measurable fun x => ∫ y, g (x, y) ∂ν :=
  hg.stronglyMeasurable.integral_prod_right'.measurable

/-! ### The chain rule -/

/-- Chain rule on a product of two probability spaces (an identity): the entropy on the product is
the average of the entropies in the first coordinate plus the entropy, in the second coordinate, of
the average over the first. Both sides are expanded and Fubini's theorem is applied to
`g log g` and `g`.
Source: Boucheron, Lugosi and Massart (2013), Chapter 4 (chain rule for entropy). -/
theorem entropy_prod_eq (μ : Measure α) (ν : Measure β)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {g : α × β → ℝ} {a b : ℝ} (ha : 0 < a) (hg : Measurable g) (hgab : ∀ z, g z ∈ Icc a b) :
    entropy (μ.prod ν) g =
      (∫ y, entropy μ (fun x => g (x, y)) ∂ν) + entropy ν (fun y => ∫ x, g (x, y) ∂μ) := by
  have hg_int : Integrable g (μ.prod ν) :=
    integrable_of_abs_le _ hg fun z => abs_le_of_mem_Icc (hgab z)
  have hgl_int := integrable_mul_log (μ.prod ν) ha hg hgab
  have hG_meas : Measurable fun y => ∫ x, g (x, y) ∂μ := measurable_integral_left μ hg
  have hG_mem : ∀ y, ∫ x, g (x, y) ∂μ ∈ Icc a b := fun y =>
    integral_mem_Icc μ (hg.comp measurable_prodMk_right) fun x => hgab _
  have hGlog_int : Integrable
      (fun y => (∫ x, g (x, y) ∂μ) * Real.log (∫ x, g (x, y) ∂μ)) ν :=
    integrable_mul_log ν ha hG_meas hG_mem
  have hA_int : Integrable (fun y => ∫ x, g (x, y) * Real.log (g (x, y)) ∂μ) ν :=
    hgl_int.integral_prod_right
  have hfubini_log : ∫ z, g z * Real.log (g z) ∂μ.prod ν =
      ∫ y, ∫ x, g (x, y) * Real.log (g (x, y)) ∂μ ∂ν := integral_prod_symm _ hgl_int
  have hfubini : ∫ z, g z ∂μ.prod ν = ∫ y, ∫ x, g (x, y) ∂μ ∂ν := integral_prod_symm _ hg_int
  simp only [entropy_eq]
  rw [integral_sub hA_int hGlog_int, hfubini_log, hfubini]
  ring

/-! ### Convexity -/

/-- Convexity of entropy: averaging over `x` before taking the entropy in `y` decreases it.
With `G = ∫ g(x, ·) dμ` and `h = log (G / E G)`, one has `E e^h = 1` and `Ent(G) = E[G h]`; Fubini
turns this into `∫ E[g(x, ·) h] dμ`, and Gibbs' inequality bounds each inner term by
`Ent(g(x, ·))`.
Source: Boucheron, Lugosi and Massart (2013), Chapter 4 (convexity of entropy). -/
theorem entropy_integral_le (μ : Measure α) (ν : Measure β)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {g : α × β → ℝ} {a b : ℝ} (ha : 0 < a) (hg : Measurable g) (hgab : ∀ z, g z ∈ Icc a b) :
    entropy ν (fun y => ∫ x, g (x, y) ∂μ) ≤ ∫ x, entropy ν (fun y => g (x, y)) ∂μ := by
  have hgl_int := integrable_mul_log (μ.prod ν) ha hg hgab
  have hG_meas : Measurable fun y => ∫ x, g (x, y) ∂μ := measurable_integral_left μ hg
  have hG_mem : ∀ y, ∫ x, g (x, y) ∂μ ∈ Icc a b := fun y =>
    integral_mem_Icc μ (hg.comp measurable_prodMk_right) fun x => hgab _
  have hG_int : Integrable (fun y => ∫ x, g (x, y) ∂μ) ν :=
    integrable_of_abs_le ν hG_meas fun y => abs_le_of_mem_Icc (hG_mem y)
  have hGlog_int : Integrable
      (fun y => (∫ x, g (x, y) ∂μ) * Real.log (∫ x, g (x, y) ∂μ)) ν :=
    integrable_mul_log ν ha hG_meas hG_mem
  have hmG_mem := integral_mem_Icc ν hG_meas hG_mem
  have hmG_pos : 0 < ∫ y, ∫ x, g (x, y) ∂μ ∂ν := ha.trans_le hmG_mem.1
  obtain ⟨mG, hmG⟩ : ∃ mG, ∫ y, ∫ x, g (x, y) ∂μ ∂ν = mG := ⟨_, rfl⟩
  rw [hmG] at hmG_pos hmG_mem
  -- The test function `h = log (G / E G)`.
  obtain ⟨h, hh_def⟩ : ∃ h : β → ℝ,
      ∀ y, h y = Real.log (∫ x, g (x, y) ∂μ) - Real.log mG :=
    ⟨fun y => Real.log (∫ x, g (x, y) ∂μ) - Real.log mG, fun _ => rfl⟩
  have hh_meas : Measurable h := by
    have hh_fun : h = fun y => Real.log (∫ x, g (x, y) ∂μ) - Real.log mG := funext hh_def
    rw [hh_fun]
    exact hG_meas.log.sub_const _
  have hh_bound : ∀ y, |h y| ≤ (|Real.log a| + |Real.log b|) + (|Real.log a| + |Real.log b|) := by
    intro y
    have hlog_y := abs_le.1 (abs_log_le_of_mem_Icc ha (hG_mem y))
    have hlog_m := abs_le.1 (abs_log_le_of_mem_Icc ha hmG_mem)
    rw [hh_def]
    exact abs_le.2 ⟨by linarith [hlog_y.1, hlog_m.2], by linarith [hlog_y.2, hlog_m.1]⟩
  have hexp_h : ∀ y, Real.exp (h y) = (∫ x, g (x, y) ∂μ) / mG := fun y => by
    rw [hh_def, Real.exp_sub, Real.exp_log (ha.trans_le (hG_mem y).1), Real.exp_log hmG_pos]
  have hexp_int : ∫ y, Real.exp (h y) ∂ν = 1 := by
    simp only [hexp_h]
    rw [integral_div, hmG, div_self hmG_pos.ne']
  -- `Ent(G) = E[G h]`.
  have hGh : ∫ y, (∫ x, g (x, y) ∂μ) * h y ∂ν =
      (∫ y, (∫ x, g (x, y) ∂μ) * Real.log (∫ x, g (x, y) ∂μ) ∂ν) -
        (∫ y, ∫ x, g (x, y) ∂μ ∂ν) * Real.log mG := by
    simp only [hh_def, mul_sub]
    rw [integral_sub hGlog_int (hG_int.mul_const _), integral_mul_const]
  have hent_eq : entropy ν (fun y => ∫ x, g (x, y) ∂μ) = ∫ y, (∫ x, g (x, y) ∂μ) * h y ∂ν := by
    rw [hGh, entropy_eq, hmG]
  -- Fubini and Gibbs.
  have hF : Integrable (fun z : α × β => g z * h z.2) (μ.prod ν) :=
    integrable_of_abs_le _ (hg.mul (hh_meas.comp measurable_snd)) fun z =>
      abs_mul_le_of_mem_Icc ha (hgab z) (hh_bound z.2)
  have hF1 : Integrable (fun x => ∫ y, g (x, y) * h y ∂ν) μ := hF.integral_prod_left
  have hF2 : Integrable (fun x => entropy ν (fun y => g (x, y))) μ := by
    simp only [entropy_eq]
    refine hgl_int.integral_prod_left.sub ?_
    exact integrable_mul_log μ ha (measurable_integral_right ν hg) fun x =>
      integral_mem_Icc ν (hg.comp measurable_prodMk_left) fun y => hgab _
  have hswap : ∫ x, ∫ y, g (x, y) * h y ∂ν ∂μ = ∫ y, ∫ x, g (x, y) * h y ∂μ ∂ν :=
    integral_integral_swap hF
  have hpull : ∫ y, (∫ x, g (x, y) ∂μ) * h y ∂ν = ∫ y, ∫ x, g (x, y) * h y ∂μ ∂ν := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    exact (integral_mul_const _ _).symm
  rw [hent_eq, hpull, ← hswap]
  exact integral_mono hF1 hF2 fun x =>
    integral_mul_le_entropy ν ha (hg.comp measurable_prodMk_left) (fun y => hgab _) hh_meas
      hh_bound hexp_int

end Entropy

end ProbabilityBasics.Concentration
