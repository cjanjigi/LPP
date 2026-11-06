/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Foundations.Concentration.Entropy
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Probability.Moments.MGFAnalytic

/-!
# Herbst's argument: an entropy bound gives a tail bound

The mathematics follows Boucheron, Lugosi and Massart (2013), Section 5.2 (Herbst's argument), with
every step written out. This is general probability and does not depend on the LPP model.

Let `X` be a bounded measurable random variable on a probability space, and suppose that its
exponentials have small entropy: `Ent(exp(s X)) ≤ c s² E exp(s X)` for every `s` in `(0, T]`.

## Main results

* `integral_exp_mul_centered_le_of_entropy_le`: then `E exp(s (X - E X)) ≤ exp(c s²)` for every `s`
  in `(0, T]`.
* `measureReal_le_sub_integral_le_of_entropy_le`: if moreover `c > 0`, then
  `P(X - E X ≥ t) ≤ exp(-t² / (4 c))` for `0 ≤ t ≤ 2 c T`.

## Proof outline

Let `Λ` be the cumulant generating function of `X` (the logarithm of `s ↦ E exp(s X)`). Since `X`
is bounded, every exponential moment is finite, so `Λ` is differentiable on all of `ℝ`, with
`Λ'(s) = E[X exp(s X)] / E exp(s X)` and `Λ'(0) = E X`. Writing the entropy of `exp(s X)` through
`log exp(s X) = s X` gives `Ent(exp(s X)) = E exp(s X) · (s Λ'(s) - Λ(s))`, so the hypothesis says
`s Λ'(s) - Λ(s) ≤ c s²`. This is the statement that `K(s) = Λ(s) / s - c s` has nonpositive
derivative on `(0, T)`, so `K` is antitone on `(0, T]`. As `s → 0⁺`, `Λ(s) / s → Λ'(0) = E X`, hence
`K(s) ≤ E X`, which is `Λ(s) ≤ s E X + c s²`. The tail bound is Chernoff's inequality with the
choice `s = t / (2 c)`.

## References

- S. Boucheron, G. Lugosi and P. Massart, *Concentration Inequalities: A Nonasymptotic Theory of
  Independence*, Oxford University Press, 2013, Section 5.2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace ProbabilityBasics.Concentration

section Herbst

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Exponential moments of a bounded variable -/

/-- A bounded measurable variable has an integrable exponential `exp (s * X)` for every real `s`:
it is bounded by `exp (|s| M)`. -/
private lemma integrable_exp_mul_of_abs_bound (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → ℝ} {M : ℝ} (hX : Measurable X) (hXM : ∀ ω, |X ω| ≤ M) (s : ℝ) :
    Integrable (fun ω => Real.exp (s * X ω)) P := by
  refine Integrable.of_bound (hX.const_mul s).exp.aestronglyMeasurable (Real.exp (|s| * M))
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_exp.2 ?_
  calc s * X ω ≤ |s * X ω| := le_abs_self _
    _ = |s| * |X ω| := abs_mul _ _
    _ ≤ |s| * M := mul_le_mul_of_nonneg_left (hXM ω) (abs_nonneg s)

/-- For a bounded measurable variable the set where `exp (s * X)` is integrable is all of `ℝ`, so
its interior is all of `ℝ` as well. This is the form in which Mathlib's cumulant generating
function calculus is stated. -/
private lemma interior_integrableExpSet_eq_univ (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → ℝ} {M : ℝ} (hX : Measurable X) (hXM : ∀ ω, |X ω| ≤ M) :
    interior (integrableExpSet X P) = univ := by
  have hall : integrableExpSet X P = univ :=
    eq_univ_of_forall fun s => integrable_exp_mul_of_abs_bound P hX hXM s
  rw [hall, interior_univ]

/-- Pulling the constant `E X` out of the exponential:
`exp (s (x - e)) = exp (-(s e)) exp (s x)`. -/
private lemma exp_mul_sub_eq (s x e : ℝ) :
    Real.exp (s * (x - e)) = Real.exp (-(s * e)) * Real.exp (s * x) := by
  rw [← Real.exp_add]
  congr 1
  ring

/-! ### The cumulant generating function of a bounded variable -/

/-- The cumulant generating function of a bounded measurable variable has derivative
`E[X exp(s X)] / E exp(s X)` at every real `s`. -/
private lemma hasDerivAt_cgf_of_abs_bound (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → ℝ} {M : ℝ} (hX : Measurable X) (hXM : ∀ ω, |X ω| ≤ M) (s : ℝ) :
    HasDerivAt (cgf X P) ((∫ ω, X ω * Real.exp (s * X ω) ∂P) / mgf X P s) s := by
  have hs : s ∈ interior (integrableExpSet X P) := by
    rw [interior_integrableExpSet_eq_univ P hX hXM]
    exact mem_univ s
  rw [← deriv_cgf hs]
  exact (analyticAt_cgf hs).differentiableAt.hasDerivAt

/-- The derivative of the cumulant generating function at `0` is the mean. -/
private lemma hasDerivAt_cgf_zero (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → ℝ} {M : ℝ} (hX : Measurable X) (hXM : ∀ ω, |X ω| ≤ M) :
    HasDerivAt (cgf X P) (∫ ω, X ω ∂P) 0 := by
  have h0 := hasDerivAt_cgf_of_abs_bound P hX hXM 0
  simpa [mgf_zero] using h0

/-- The entropy of `exp (s X)`: since `log (exp (s X)) = s X`, it equals
`s E[X exp(s X)] - m log m` with `m = E exp(s X)`. -/
private lemma entropy_exp_mul_eq (P : Measure Ω) (X : Ω → ℝ) (s : ℝ) :
    entropy P (fun ω => Real.exp (s * X ω)) =
      s * (∫ ω, X ω * Real.exp (s * X ω) ∂P) - mgf X P s * Real.log (mgf X P s) := by
  have hmgf : ∫ ω, Real.exp (s * X ω) ∂P = mgf X P s := rfl
  have hlog : ∫ ω, Real.exp (s * X ω) * Real.log (Real.exp (s * X ω)) ∂P =
      s * ∫ ω, X ω * Real.exp (s * X ω) ∂P := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Real.log_exp]
    ring
  rw [entropy_eq, hlog, hmgf]

/-- A real inequality: from `s A - m log m ≤ B m` with `m > 0` one gets
`s (A / m) - log m ≤ B`. -/
private lemma mul_div_sub_log_le {s A m B : ℝ} (hm : 0 < m)
    (h : s * A - m * Real.log m ≤ B * m) : s * (A / m) - Real.log m ≤ B := by
  have hrewrite : s * (A / m) - Real.log m = (s * A - m * Real.log m) / m := by
    field_simp
  rw [hrewrite, div_le_iff₀ hm]
  exact h

/-- The entropy hypothesis in terms of the cumulant generating function `Λ`: for `s` in `(0, T]`,
`s Λ'(s) - Λ(s) ≤ c s²`, where `Λ'(s) = E[X exp(s X)] / E exp(s X)`. -/
private lemma mul_deriv_cgf_sub_cgf_le (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → ℝ} {M c T : ℝ} (hX : Measurable X) (hXM : ∀ ω, |X ω| ≤ M)
    (hent : ∀ s ∈ Ioc 0 T, entropy P (fun ω => Real.exp (s * X ω)) ≤
      c * s ^ 2 * ∫ ω, Real.exp (s * X ω) ∂P)
    {s : ℝ} (hs : s ∈ Ioc 0 T) :
    s * ((∫ ω, X ω * Real.exp (s * X ω) ∂P) / mgf X P s) - cgf X P s ≤ c * s ^ 2 := by
  have hm : 0 < mgf X P s := mgf_pos (integrable_exp_mul_of_abs_bound P hX hXM s)
  have hentropy := hent s hs
  rw [entropy_exp_mul_eq] at hentropy
  exact mul_div_sub_log_le hm hentropy

/-! ### Herbst's argument -/

/-- Herbst's argument on an interval `(0, T]`: if `Ent(exp(s X)) ≤ c s² E exp(s X)` for every `s` in
`(0, T]`, then `E exp(s (X - E X)) ≤ exp(c s²)` there. The cumulant generating function `Λ` of `X`
satisfies `s Λ'(s) - Λ(s) ≤ c s²`, so `Λ(s) / s - c s` is antitone on `(0, T]`; its limit at `0⁺`
is `Λ'(0) = E X`, which gives `Λ(s) ≤ s E X + c s²`.
Source: Boucheron, Lugosi and Massart (2013), Section 5.2 (Herbst's argument). -/
theorem integral_exp_mul_centered_le_of_entropy_le (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → ℝ} {M c T : ℝ} (hX : Measurable X) (hXM : ∀ ω, |X ω| ≤ M)
    (hent : ∀ s ∈ Ioc 0 T, entropy P (fun ω => Real.exp (s * X ω)) ≤
      c * s ^ 2 * ∫ ω, Real.exp (s * X ω) ∂P)
    {s : ℝ} (hs : s ∈ Ioc 0 T) :
    ∫ ω, Real.exp (s * (X ω - ∫ η, X η ∂P)) ∂P ≤ Real.exp (c * s ^ 2) := by
  -- `K r = Λ r / r - c r` is the function whose monotonicity is Herbst's argument.
  have hK_deriv : ∀ r : ℝ, 0 < r → HasDerivAt (fun r => cgf X P r / r - c * r)
      ((r * ((∫ ω, X ω * Real.exp (r * X ω) ∂P) / mgf X P r) - cgf X P r) / r ^ 2 - c) r := by
    intro r hr
    have hquotient := (hasDerivAt_cgf_of_abs_bound P hX hXM r).div (hasDerivAt_id' r) hr.ne'
    have hdifference := hquotient.sub ((hasDerivAt_id' r).const_mul c)
    exact hdifference.congr_deriv (by ring)
  have hK_anti : AntitoneOn (fun r => cgf X P r / r - c * r) (Ioc 0 T) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ioc 0 T) ?_ ?_ ?_
    · exact fun r hr => (hK_deriv r hr.1).continuousAt.continuousWithinAt
    · rw [interior_Ioc]
      exact fun r hr => (hK_deriv r hr.1).differentiableAt.differentiableWithinAt
    · rw [interior_Ioc]
      intro r hr
      rw [(hK_deriv r hr.1).deriv]
      have hbound := mul_deriv_cgf_sub_cgf_le P hX hXM hent (s := r) ⟨hr.1, hr.2.le⟩
      have hr_sq : 0 < r ^ 2 := by have := hr.1; positivity
      have hquotient_le : (r * ((∫ ω, X ω * Real.exp (r * X ω) ∂P) / mgf X P r) - cgf X P r) /
          r ^ 2 ≤ c := by
        rw [div_le_iff₀ hr_sq]
        linarith
      linarith
  -- The limit of `K` at `0⁺` is the mean.
  have hc_tendsto : Tendsto (fun r : ℝ => c * r) (𝓝[>] 0) (𝓝 0) := by
    have hcont : Tendsto (fun r : ℝ => c * r) (𝓝 0) (𝓝 (c * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at hcont
    exact hcont.mono_left nhdsWithin_le_nhds
  have hK_tendsto : Tendsto (fun r => cgf X P r / r - c * r) (𝓝[>] 0) (𝓝 (∫ ω, X ω ∂P)) := by
    have hslope := (hasDerivAt_cgf_zero P hX hXM).tendsto_slope_zero_right
    have hdiff := hslope.sub hc_tendsto
    rw [sub_zero] at hdiff
    refine hdiff.congr fun r => ?_
    simp [div_eq_inv_mul]
  -- `K s ≤ E X`, that is `Λ s ≤ s E X + c s²`.
  have hK_le : cgf X P s / s - c * s ≤ ∫ ω, X ω ∂P := by
    refine ge_of_tendsto hK_tendsto ?_
    filter_upwards [Ioo_mem_nhdsGT hs.1] with r hr
    exact hK_anti ⟨hr.1, hr.2.le.trans hs.2⟩ hs hr.2.le
  have hcgf_le : cgf X P s ≤ s * (∫ ω, X ω ∂P) + c * s ^ 2 := by
    have hmul : cgf X P s ≤ ((∫ ω, X ω ∂P) + c * s) * s := by
      rw [← div_le_iff₀ hs.1]
      linarith
    linarith
  -- Assemble: `E exp(s (X - E X)) = exp (Λ s - s E X) ≤ exp (c s²)`.
  have hm : 0 < mgf X P s := mgf_pos (integrable_exp_mul_of_abs_bound P hX hXM s)
  have hcentered : ∫ ω, Real.exp (s * (X ω - ∫ η, X η ∂P)) ∂P =
      Real.exp (-(s * ∫ η, X η ∂P)) * mgf X P s := by
    simp only [exp_mul_sub_eq]
    rw [integral_const_mul]
    rfl
  have hmgf_eq : mgf X P s = Real.exp (cgf X P s) := (Real.exp_log hm).symm
  rw [hcentered, hmgf_eq, ← Real.exp_add]
  exact Real.exp_le_exp.2 (by linarith)

/-! ### Chernoff's bound -/

/-- Chernoff's bound after Herbst's argument, for thresholds `t ≤ 2 c T`: under the entropy
hypothesis of Herbst's argument and `c > 0`, `P(X - E X ≥ t) ≤ exp(-t² / (4 c))`. For `t > 0` take
`s = t / (2 c)` in Chernoff's inequality `P(Y ≥ t) ≤ exp(-s t) E exp(s Y)` and bound the exponential
moment by Herbst's argument; `t = 0` is the trivial bound by `1`.
Source: Boucheron, Lugosi and Massart (2013), Section 5.2. -/
theorem measureReal_le_sub_integral_le_of_entropy_le (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → ℝ} {M c T : ℝ} (hX : Measurable X) (hXM : ∀ ω, |X ω| ≤ M) (hc : 0 < c)
    (hent : ∀ s ∈ Ioc 0 T, entropy P (fun ω => Real.exp (s * X ω)) ≤
      c * s ^ 2 * ∫ ω, Real.exp (s * X ω) ∂P)
    {t : ℝ} (ht : 0 ≤ t) (htT : t ≤ 2 * c * T) :
    P.real {ω | t ≤ X ω - ∫ η, X η ∂P} ≤ Real.exp (-t ^ 2 / (4 * c)) := by
  rcases ht.eq_or_lt with ht_zero | ht_pos
  · -- `t = 0`: the probability is at most `1 = exp 0`.
    rw [← ht_zero]
    calc P.real {ω | 0 ≤ X ω - ∫ η, X η ∂P} ≤ 1 := measureReal_le_one
      _ = Real.exp (-0 ^ 2 / (4 * c)) := by simp
  · -- `t > 0`: Chernoff with `s = t / (2 c)`.
    obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = t / (2 * c) := ⟨_, rfl⟩
    have hc_ne : c ≠ 0 := hc.ne'
    have hs_pos : 0 < s := by rw [hs_def]; positivity
    have hs_le : s ≤ T := by
      rw [hs_def, div_le_iff₀ (by positivity)]
      linarith
    have hs : s ∈ Ioc 0 T := ⟨hs_pos, hs_le⟩
    have hY_int : Integrable (fun ω => Real.exp (s * (X ω - ∫ η, X η ∂P))) P := by
      simp only [exp_mul_sub_eq]
      exact (integrable_exp_mul_of_abs_bound P hX hXM s).const_mul _
    have hchernoff := measure_ge_le_exp_mul_mgf (μ := P) (X := fun ω => X ω - ∫ η, X η ∂P) t
      hs_pos.le hY_int
    have hherbst := integral_exp_mul_centered_le_of_entropy_le P hX hXM hent hs
    have hexponent : -s * t + c * s ^ 2 = -t ^ 2 / (4 * c) := by
      rw [hs_def]
      field_simp
      ring
    calc P.real {ω | t ≤ X ω - ∫ η, X η ∂P}
        ≤ Real.exp (-s * t) * mgf (fun ω => X ω - ∫ η, X η ∂P) P s := hchernoff
      _ ≤ Real.exp (-s * t) * Real.exp (c * s ^ 2) :=
          mul_le_mul_of_nonneg_left hherbst (Real.exp_nonneg _)
      _ = Real.exp (-t ^ 2 / (4 * c)) := by rw [← Real.exp_add, hexponent]

end Herbst

end ProbabilityBasics.Concentration
