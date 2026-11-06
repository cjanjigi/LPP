/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Foundations.Concentration.Tensorization

/-!
# The modified logarithmic Sobolev inequality on a finite product

The mathematics follows Massart (2000) and Boucheron, Lugosi and Massart (2013), Theorem 6.6, with
every step written out. This is general probability and does not depend on the LPP model.

## Main result

Let `μ i` be probability measures on the coordinate spaces `E i`, `i : Fin n`, and
`P = Measure.pi μ`. Let `G` be measurable and bounded, and let `a` be a fixed point of the product.
Put `G_i x = G (update x i (a i))`, the value of `G` after resetting coordinate `i` to `a i`, and
`φ z = e^z - z - 1`.

* `entropy_exp_pi_le_sum`: `Ent_P(e^G) ≤ ∑ i, ∫ e^G φ(G_i - G) dP`.

## Proof outline

Tensorization (`entropy_pi_le_sum`) applied to `e^G` bounds `Ent_P(e^G)` by the sum over `i` of the
averages of the entropy in coordinate `i`. Fix `i` and the other coordinates `x`. The number
`c = G_i x` does not depend on coordinate `i`, so the variational bound
`entropy_le_integral_of_pos` with the constant `u = e^c` bounds the coordinate entropy by an
integral over the coordinate `t`. Its integrand is, as an exact algebraic identity, the function
`F = e^G φ(G_i - G)` evaluated at `update x i t`. Integrating over `x` and using
`integral_integral_update` turns the average of these coordinate integrals into `∫ F dP`.

## References

- P. Massart, *About the constants in Talagrand's concentration inequalities for empirical
  processes*, Ann. Probab. 28 (2000).
- S. Boucheron, G. Lugosi and P. Massart, *Concentration Inequalities: A Nonasymptotic Theory of
  Independence*, Oxford University Press, 2013, Theorem 6.6.
-/

@[expose] public section

open MeasureTheory Set

namespace ProbabilityBasics.Concentration

section Helpers

variable {α : Type*} [MeasurableSpace α]

/-! ### Boundedness of the objects that are integrated -/

/-- If `|h| ≤ M`, the mean of `e^h` lies in `[e^{-M}, e^M]`. -/
private lemma integral_exp_mem_Icc (ν : Measure α) [IsProbabilityMeasure ν] {h : α → ℝ} {M : ℝ}
    (hh : Measurable h) (hhM : ∀ t, |h t| ≤ M) :
    ∫ t, Real.exp (h t) ∂ν ∈ Icc (Real.exp (-M)) (Real.exp M) := by
  have hupper : ∀ t, Real.exp (h t) ≤ Real.exp M := fun t =>
    Real.exp_le_exp.2 (le_trans (le_abs_self _) (hhM t))
  have hlower : ∀ t, Real.exp (-M) ≤ Real.exp (h t) := fun t =>
    Real.exp_le_exp.2 (by linarith [abs_le.1 (hhM t)])
  have hint : Integrable (fun t => Real.exp (h t)) ν :=
    integrable_of_abs_le ν hh.exp fun t => by
      rw [abs_of_pos (Real.exp_pos _)]
      exact hupper t
  constructor
  · simpa using integral_mono (integrable_const (Real.exp (-M))) hint hlower
  · simpa using integral_mono hint (integrable_const (Real.exp M)) hupper

/-- The entropy of `e^h`, with `|h| ≤ M`, is bounded by `2 e^M M`: both `E[e^h log e^h]` and
`E e^h log E e^h` are bounded by `e^M M`. -/
private lemma abs_entropy_exp_le (ν : Measure α) [IsProbabilityMeasure ν] {h : α → ℝ} {M : ℝ}
    (hh : Measurable h) (hhM : ∀ t, |h t| ≤ M) :
    |entropy ν (fun t => Real.exp (h t))| ≤ 2 * (Real.exp M * M) := by
  have hm := integral_exp_mem_Icc ν hh hhM
  have hm_pos : 0 < ∫ t, Real.exp (h t) ∂ν := (Real.exp_pos _).trans_le hm.1
  have hlog_m : |Real.log (∫ t, Real.exp (h t) ∂ν)| ≤ M := by
    rw [abs_le]
    constructor
    · calc -M = Real.log (Real.exp (-M)) := (Real.log_exp _).symm
        _ ≤ _ := Real.log_le_log (Real.exp_pos _) hm.1
    · calc _ ≤ Real.log (Real.exp M) := Real.log_le_log hm_pos hm.2
        _ = M := Real.log_exp _
  have hterm : |(∫ t, Real.exp (h t) ∂ν) * Real.log (∫ t, Real.exp (h t) ∂ν)| ≤
      Real.exp M * M := by
    rw [abs_mul, abs_of_pos hm_pos]
    exact mul_le_mul hm.2 hlog_m (abs_nonneg _) (Real.exp_pos _).le
  have hpoint : ∀ t, |Real.exp (h t) * Real.log (Real.exp (h t))| ≤ Real.exp M * M := fun t => by
    rw [Real.log_exp, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (Real.exp_le_exp.2 (le_trans (le_abs_self _) (hhM t))) (hhM t)
      (abs_nonneg _) (Real.exp_pos _).le
  have hint : |∫ t, Real.exp (h t) * Real.log (Real.exp (h t)) ∂ν| ≤ Real.exp M * M := by
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
      norm_integral_le_of_norm_le_const (μ := ν)
        (f := fun t => Real.exp (h t) * Real.log (Real.exp (h t))) (C := Real.exp M * M)
        (ae_of_all _ fun t => by simpa only [Real.norm_eq_abs] using hpoint t)
  rw [entropy_eq]
  have hint' := abs_le.1 hint
  have hterm' := abs_le.1 hterm
  exact abs_le.2 ⟨by linarith [hint'.1, hint'.2, hterm'.1, hterm'.2],
    by linarith [hint'.1, hint'.2, hterm'.1, hterm'.2]⟩

/-- The integrand `e^p φ(q - p)` is bounded by `e^M (e^{2M} + 2M + 1)` when `|p|, |q| ≤ M`. -/
private lemma abs_exp_mul_phi_le {p q M : ℝ} (hp : |p| ≤ M) (hq : |q| ≤ M) :
    |Real.exp p * (Real.exp (q - p) - (q - p) - 1)| ≤
      Real.exp M * (Real.exp (2 * M) + 2 * M + 1) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans hp
  have hd2 : |q - p| ≤ 2 * M := by
    have := abs_sub q p
    linarith
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  refine mul_le_mul (Real.exp_le_exp.2 (le_trans (le_abs_self _) hp)) ?_ (abs_nonneg _)
    (Real.exp_pos _).le
  have hexp_le : Real.exp (q - p) ≤ Real.exp (2 * M) :=
    Real.exp_le_exp.2 (le_trans (le_abs_self _) hd2)
  have hexp_pos : 0 < Real.exp (q - p) := Real.exp_pos _
  have hd2' := abs_le.1 hd2
  rw [abs_le]
  constructor <;> nlinarith [Real.add_one_le_exp (q - p)]

end Helpers

section Pi

variable {n : ℕ} {E : Fin n → Type*} [∀ i, MeasurableSpace (E i)]
  (μ : ∀ i, Measure (E i)) [∀ i, IsProbabilityMeasure (μ i)]

/-! ### Measurability of the coordinate integrals -/

/-- Integrating a measurable function over coordinate `i`, as a function of the other coordinates,
gives a measurable function. -/
private lemma measurable_integral_update (i : Fin n) {h : (∀ j, E j) → ℝ} (hh : Measurable h) :
    Measurable fun x => ∫ t, h (Function.update x i t) ∂μ i :=
  (hh.comp (measurable_update' (a := i))).stronglyMeasurable.integral_prod_right'.measurable

/-- The entropy in coordinate `i`, as a function of the remaining coordinates, is measurable. -/
private lemma measurable_entropy_update (i : Fin n) {g : (∀ j, E j) → ℝ} (hg : Measurable g) :
    Measurable fun x => entropy (μ i) (fun t => g (Function.update x i t)) := by
  simp only [entropy_eq]
  exact (measurable_integral_update μ i (hg.mul hg.log)).sub
    ((measurable_integral_update μ i hg).mul (measurable_integral_update μ i hg).log)

/-! ### One coordinate -/

/-- The coordinate step. Let `F = e^G φ(G_i - G)`. Averaging the coordinate-`i` entropy of `e^G`
over the other coordinates is at most `∫ F dP`. For each `x`, the variational bound with the
constant `u = e^{G_i x}` bounds the entropy by `∫ F(update x i t) dμ_i(t)`; then
`integral_integral_update` removes the inner integral. -/
private lemma integral_entropy_update_le {G : (∀ j, E j) → ℝ} {M : ℝ} (hG : Measurable G)
    (hGM : ∀ x, |G x| ≤ M) (a : ∀ j, E j) (i : Fin n) {F : (∀ j, E j) → ℝ} {K : ℝ}
    (hFm : Measurable F) (hFK : ∀ y, |F y| ≤ K)
    (hF : ∀ y, F y = Real.exp (G y) * (Real.exp (G (Function.update y i (a i)) - G y) -
      (G (Function.update y i (a i)) - G y) - 1)) :
    ∫ x, entropy (μ i) (fun t => Real.exp (G (Function.update x i t))) ∂Measure.pi μ ≤
      ∫ x, F x ∂Measure.pi μ := by
  -- Pointwise in `x`: the variational bound with `u = e^{G_i x}`, then the algebraic identity.
  have hpoint : ∀ x, entropy (μ i) (fun t => Real.exp (G (Function.update x i t))) ≤
      ∫ t, F (Function.update x i t) ∂μ i := by
    intro x
    have hGt : Measurable fun t => G (Function.update x i t) :=
      hG.comp (measurable_update x (a := i))
    have hvar := entropy_le_integral_of_pos (μ i)
      (g := fun t => Real.exp (G (Function.update x i t)))
      (a := Real.exp (-(M))) (b := Real.exp M) (Real.exp_pos _) hGt.exp
      (fun t => ⟨Real.exp_le_exp.2 (by linarith [abs_le.1 (hGM (Function.update x i t))]),
        Real.exp_le_exp.2 (le_trans (le_abs_self _) (hGM _))⟩)
      (u := Real.exp (G (Function.update x i (a i)))) (Real.exp_pos _)
    refine hvar.trans (le_of_eq (integral_congr_ae (ae_of_all _ fun t => ?_)))
    have hexp : Real.exp (G (Function.update x i t)) *
        Real.exp (G (Function.update x i (a i)) - G (Function.update x i t)) =
        Real.exp (G (Function.update x i (a i))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    simp only [hF, Function.update_idem, Real.log_exp]
    linear_combination (-1 : ℝ) * hexp
  -- Integrability of both sides as functions of `x`.
  have hlhs_int : Integrable
      (fun x => entropy (μ i) (fun t => Real.exp (G (Function.update x i t)))) (Measure.pi μ) :=
    integrable_of_abs_le _ (measurable_entropy_update μ i hG.exp) fun x =>
      abs_entropy_exp_le (μ i) (hG.comp (measurable_update x (a := i))) fun t => hGM _
  have hrhs_int : Integrable (fun x => ∫ t, F (Function.update x i t) ∂μ i) (Measure.pi μ) :=
    integrable_of_abs_le _ (measurable_integral_update μ i hFm) fun x => by
      simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
        norm_integral_le_of_norm_le_const (μ := μ i) (f := fun t => F (Function.update x i t))
          (C := K) (ae_of_all _ fun t => by simpa only [Real.norm_eq_abs] using hFK _)
  calc ∫ x, entropy (μ i) (fun t => Real.exp (G (Function.update x i t))) ∂Measure.pi μ
      ≤ ∫ x, (∫ t, F (Function.update x i t) ∂μ i) ∂Measure.pi μ :=
        integral_mono hlhs_int hrhs_int hpoint
    _ = ∫ x, F x ∂Measure.pi μ := integral_integral_update μ i hFm hFK

/-! ### The modified logarithmic Sobolev inequality -/

/-- Modified logarithmic Sobolev inequality (Massart 2000; Boucheron, Lugosi and Massart 2013,
Theorem 6.6), with the comparison value of coordinate `i` obtained by setting coordinate `i` to the
fixed point `a i`. For a measurable bounded `G` on a finite product of probability spaces,
`Ent(e^G) ≤ ∑ i, E[e^G φ(G_i - G)]`, where `G_i x = G (update x i (a i))` and
`φ z = e^z - z - 1`. The proof applies tensorization to `e^G`, bounds each coordinate entropy with
the constant `u = e^{G_i}` (which does not depend on coordinate `i`), and integrates out the
coordinate with `integral_integral_update`.
Martin (2004), Lemma 3.1 uses it through Martin (2002), Lemma 5.1. -/
theorem entropy_exp_pi_le_sum {G : (∀ j, E j) → ℝ} {M : ℝ} (hG : Measurable G)
    (hGM : ∀ x, |G x| ≤ M) (a : ∀ j, E j) :
    entropy (Measure.pi μ) (fun x => Real.exp (G x)) ≤
      ∑ i, ∫ x, Real.exp (G x) *
        (Real.exp (G (Function.update x i (a i)) - G x) -
          (G (Function.update x i (a i)) - G x) - 1) ∂Measure.pi μ := by
  -- Step 1: tensorization for `g = e^G`, which takes values in `[e^{-M}, e^M]`.
  have htensor := entropy_pi_le_sum μ (g := fun x => Real.exp (G x))
    (a := Real.exp (-(M))) (b := Real.exp M) (Real.exp_pos _) hG.exp
    (fun x => ⟨Real.exp_le_exp.2 (by linarith [abs_le.1 (hGM x)]),
      Real.exp_le_exp.2 (le_trans (le_abs_self _) (hGM x))⟩)
  refine htensor.trans (Finset.sum_le_sum fun i _ => ?_)
  -- Steps 2 and 3: one coordinate, with `F = e^G φ(G_i - G)` measurable and bounded.
  have hGi : Measurable fun y => G (Function.update y i (a i)) :=
    hG.comp measurable_update_left
  have hdiff : Measurable fun y => G (Function.update y i (a i)) - G y := hGi.sub hG
  exact integral_entropy_update_le μ hG hGM a i
    (F := fun y => Real.exp (G y) * (Real.exp (G (Function.update y i (a i)) - G y) -
      (G (Function.update y i (a i)) - G y) - 1))
    (K := Real.exp M * (Real.exp (2 * M) + 2 * M + 1))
    (hG.exp.mul ((hdiff.exp.sub hdiff).sub measurable_const))
    (fun y => abs_exp_mul_phi_le (hGM y) (hGM _)) fun _ => rfl

end Pi

end ProbabilityBasics.Concentration
