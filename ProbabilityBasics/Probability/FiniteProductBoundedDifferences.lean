/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.MeasureTheory.Integral.Pi
public import ProbabilityBasics.Probability.FiberHoeffding
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-!
# Finite product splitting and integrals in one coordinate

The coordinate spaces and probability laws may differ. The integral in the first coordinate is
the integral of the function with the other coordinates held fixed. The file uses
this splitting to prove the centered exponential estimate for a finite product by induction.
-/

public section

open MeasureTheory

namespace LPPDifferentiability

section FinSucc

variable {n : ℕ} {E : Fin (n + 1) → Type*}
  [∀ i, MeasurableSpace (E i)]
  (μ : ∀ i, Measure (E i)) [∀ i, IsProbabilityMeasure (μ i)]

/-- The integral over a finite product, after separating the first coordinate. -/
theorem integral_pi_fin_succ (F : (∀ i, E i) → ℝ) :
    (∫ x, F x ∂Measure.pi μ) =
      ∫ p : E 0 × (∀ j : Fin n, E ((0 : Fin (n + 1)).succAbove j)),
        F ((0 : Fin (n + 1)).insertNth p.1 p.2)
        ∂(μ 0).prod (Measure.pi fun j => μ ((0 : Fin (n + 1)).succAbove j)) := by
  exact (((measurePreserving_piFinSuccAbove μ 0).symm).integral_comp' F).symm

/-- Insertion gives a jointly measurable first-coordinate representation. -/
theorem measurable_fin_head {F : (∀ i, E i) → ℝ} (hF : Measurable F) :
    Measurable (fun p : E 0 × (∀ j : Fin n, E ((0 : Fin (n + 1)).succAbove j)) =>
      F ((0 : Fin (n + 1)).insertNth p.1 p.2)) :=
  hF.comp (MeasurableEquiv.piFinSuccAbove E 0).symm.measurable

/-- The first-coordinate integral is measurable in the remaining coordinates. -/
theorem measurable_integral_fin_head {F : (∀ i, E i) → ℝ} (hF : Measurable F) :
    Measurable (fun r : ∀ j : Fin n, E ((0 : Fin (n + 1)).succAbove j) =>
      ∫ x, F ((0 : Fin (n + 1)).insertNth x r) ∂μ 0) :=
  (measurable_fin_head hF).stronglyMeasurable.integral_prod_left'.measurable

/-- Every first-coordinate section of a bounded measurable function is integrable. -/
theorem integrable_fin_head {F : (∀ i, E i) → ℝ} {M : ℝ}
    (hF : Measurable F) (hbound : ∀ x, |F x| ≤ M)
    (r : ∀ j : Fin n, E ((0 : Fin (n + 1)).succAbove j)) :
    Integrable (fun x => F ((0 : Fin (n + 1)).insertNth x r)) (μ 0) := by
  refine Integrable.of_bound
    ((measurable_fin_head hF).comp measurable_prodMk_right).aestronglyMeasurable M ?_
  exact ae_of_all _ fun x => by
    simpa only [Real.norm_eq_abs] using hbound ((0 : Fin (n + 1)).insertNth x r)

/-- Averaging one coordinate preserves a global absolute bound. -/
theorem abs_integral_fin_head_le {F : (∀ i, E i) → ℝ} {M : ℝ}
    (hbound : ∀ x, |F x| ≤ M)
    (r : ∀ j : Fin n, E ((0 : Fin (n + 1)).succAbove j)) :
    |∫ x, F ((0 : Fin (n + 1)).insertNth x r) ∂μ 0| ≤ M := by
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := μ 0)
      (f := fun x => F ((0 : Fin (n + 1)).insertNth x r)) (C := M)
      (ae_of_all _ fun x => by
        simpa only [Real.norm_eq_abs] using hbound ((0 : Fin (n + 1)).insertNth x r))

/-- The first-coordinate average of a bounded function is integrable under the law of the other
coordinates. -/
theorem integrable_integral_fin_head {F : (∀ i, E i) → ℝ} {M : ℝ}
    (hF : Measurable F) (hbound : ∀ x, |F x| ≤ M) :
    Integrable (fun r : ∀ j : Fin n, E ((0 : Fin (n + 1)).succAbove j) =>
      ∫ x, F ((0 : Fin (n + 1)).insertNth x r) ∂μ 0)
      (Measure.pi fun j => μ ((0 : Fin (n + 1)).succAbove j)) := by
  refine Integrable.of_bound
    (measurable_integral_fin_head μ hF).aestronglyMeasurable M ?_
  exact ae_of_all _ fun r => by
    simpa only [Real.norm_eq_abs] using abs_integral_fin_head_le μ hbound r

/-- Averaging one coordinate preserves the update bound in every remaining coordinate. -/
theorem abs_integral_fin_head_update_sub_le {F : (∀ i, E i) → ℝ} {M b : ℝ}
    (hF : Measurable F) (hbound : ∀ x, |F x| ≤ M)
    (hosc : ∀ x i y, |F (Function.update x i y) - F x| ≤ b)
    (r : ∀ j : Fin n, E ((0 : Fin (n + 1)).succAbove j))
    (i : Fin n) (y : E ((0 : Fin (n + 1)).succAbove i)) :
    |(∫ x, F ((0 : Fin (n + 1)).insertNth x (Function.update r i y)) ∂μ 0) -
      (∫ x, F ((0 : Fin (n + 1)).insertNth x r) ∂μ 0)| ≤ b := by
  classical
  rw [← integral_sub (integrable_fin_head μ hF hbound _) (integrable_fin_head μ hF hbound _)]
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := μ 0)
      (f := fun x => F ((0 : Fin (n + 1)).insertNth x (Function.update r i y)) -
        F ((0 : Fin (n + 1)).insertNth x r)) (C := b)
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, Fin.insertNth_update]
        exact hosc _ _ _)

end FinSucc

/-- The centered exponential estimate for heterogeneous finite products. -/
theorem integral_exp_centered_pi_le {n : ℕ} {E : Fin n → Type*}
    [∀ i, MeasurableSpace (E i)] (μ : ∀ i, Measure (E i))
    [∀ i, IsProbabilityMeasure (μ i)] {F : (∀ i, E i) → ℝ} {M b : ℝ}
    (hM : 0 ≤ M) (hb : 0 ≤ b) (hF : Measurable F)
    (hbound : ∀ x, |F x| ≤ M)
    (hosc : ∀ x i y, |F (Function.update x i y) - F x| ≤ b) (t : ℝ) :
    (∫ x, Real.exp (t * (F x - ∫ z, F z ∂Measure.pi μ)) ∂Measure.pi μ) ≤
      Real.exp ((n : ℝ) * b ^ 2 * t ^ 2 / 2) := by
  induction n generalizing M b t with
  | zero =>
    let x₀ : ∀ i : Fin 0, E i := fun i => Fin.elim0 i
    have hval (x : ∀ i : Fin 0, E i) : F x = F x₀ :=
      congrArg F (Subsingleton.elim x x₀)
    have hmean : (∫ z, F z ∂Measure.pi μ) = F x₀ :=
      integral_eq_const (ae_of_all _ hval)
    calc
      _ = ∫ _x : ∀ i : Fin 0, E i, (1 : ℝ) ∂Measure.pi μ := by
        apply integral_congr_ae
        exact ae_of_all _ fun x => by
          change Real.exp (t * (F x - ∫ z, F z ∂Measure.pi μ)) = 1
          rw [hmean, hval x, sub_self, mul_zero, Real.exp_zero]
      _ ≤ Real.exp (((0 : ℕ) : ℝ) * b ^ 2 * t ^ 2 / 2) := by
        simp only [integral_const, probReal_univ, one_smul,
          Nat.cast_zero, zero_mul, zero_div, Real.exp_zero, le_refl]
  | succ n ih =>
    let μr := fun j : Fin n => μ ((0 : Fin (n + 1)).succAbove j)
    let f : E 0 × (∀ j : Fin n, E ((0 : Fin (n + 1)).succAbove j)) → ℝ :=
      fun p => F ((0 : Fin (n + 1)).insertNth p.1 p.2)
    let G := fun r : ∀ j : Fin n, E ((0 : Fin (n + 1)).succAbove j) =>
      ∫ x, F ((0 : Fin (n + 1)).insertNth x r) ∂μ 0
    have hf : Measurable f := measurable_fin_head hF
    have hfb : ∀ p, |f p| ≤ M := fun p => hbound _
    have hfi : Integrable f ((μ 0).prod (Measure.pi μr)) := by
      refine Integrable.of_bound hf.aestronglyMeasurable M ?_
      exact ae_of_all _ fun p => by simpa only [Real.norm_eq_abs] using hfb p
    have hmean : (∫ p, f p ∂(μ 0).prod (Measure.pi μr)) =
        ∫ r, G r ∂Measure.pi μr := integral_prod_symm f hfi
    have hsplit : (∫ x, F x ∂Measure.pi μ) =
        ∫ p, f p ∂(μ 0).prod (Measure.pi μr) := integral_pi_fin_succ μ F
    have hfo : ∀ r x y, |f (x, r) - f (y, r)| ≤ b := by
      intro r x y
      simpa only [Fin.update_insertNth] using
        hosc ((0 : Fin (n + 1)).insertNth y r) 0 x
    have hstep := integral_exp_sub_integral_le_fiber
      (μ 0) (Measure.pi μr) f M b hM hb hf hfb hfo t
    have hG := ih (μ := μr) (F := G) (M := M) (b := b) (t := t)
      hM hb (measurable_integral_fin_head μ hF)
      (abs_integral_fin_head_le μ hbound)
      (abs_integral_fin_head_update_sub_le μ hF hbound hosc)
    calc
      _ = ∫ p, Real.exp (t * (f p - ∫ z, f z ∂(μ 0).prod (Measure.pi μr)))
            ∂(μ 0).prod (Measure.pi μr) := by
        rw [integral_pi_fin_succ μ, hsplit]
      _ ≤ Real.exp (b ^ 2 * t ^ 2 / 2) *
          ∫ r, Real.exp (t * (G r - ∫ p, f p ∂(μ 0).prod (Measure.pi μr)))
            ∂Measure.pi μr := hstep
      _ = Real.exp (b ^ 2 * t ^ 2 / 2) *
          ∫ r, Real.exp (t * (G r - ∫ z, G z ∂Measure.pi μr))
            ∂Measure.pi μr := by rw [hmean]
      _ ≤ Real.exp (b ^ 2 * t ^ 2 / 2) * Real.exp ((n : ℝ) * b ^ 2 * t ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left hG (Real.exp_pos _).le
      _ = Real.exp (((n + 1 : ℕ) : ℝ) * b ^ 2 * t ^ 2 / 2) := by
        rw [← Real.exp_add, Nat.cast_add, Nat.cast_one]
        congr 1
        ring

end LPPDifferentiability
