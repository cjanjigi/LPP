/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.FiniteProductBoundedDifferences
public import ProbabilityBasics.Probability.SharpFiberHoeffding
public import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Sharp concentration for heterogeneous finite products

Bounded coordinate oscillations give a sharp centered MGF estimate on a
finite product. The one-sided tail uses the actual centered function and its
actual product law.
-/

public section

open MeasureTheory ProbabilityTheory

namespace LPPDifferentiability

/-- The sharp centered MGF estimate for a heterogeneous finite product. -/
theorem integral_exp_centered_pi_le_sharp {n : ℕ} {E : Fin n → Type*}
    [∀ i, MeasurableSpace (E i)] (μ : ∀ i, Measure (E i))
    [∀ i, IsProbabilityMeasure (μ i)] {F : (∀ i, E i) → ℝ} {M b : ℝ}
    (hM : 0 ≤ M) (hb : 0 ≤ b) (hF : Measurable F)
    (hbound : ∀ x, |F x| ≤ M)
    (hosc : ∀ x i y, |F (Function.update x i y) - F x| ≤ b) (t : ℝ) :
    (∫ x, Real.exp (t * (F x - ∫ z, F z ∂Measure.pi μ)) ∂Measure.pi μ) ≤
      Real.exp ((n : ℝ) * b ^ 2 * t ^ 2 / 8) := by
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
      _ ≤ Real.exp (((0 : ℕ) : ℝ) * b ^ 2 * t ^ 2 / 8) := by
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
    have hstep := integral_exp_sub_integral_le_fiber_sharp
      (μ 0) (Measure.pi μr) f M b hb hf hfb hfo t
    have hG := ih (μ := μr) (F := G) (M := M) (b := b) (t := t)
      hM hb (measurable_integral_fin_head μ hF)
      (abs_integral_fin_head_le μ hbound)
      (abs_integral_fin_head_update_sub_le μ hF hbound hosc)
    calc
      _ = ∫ p, Real.exp (t * (f p - ∫ z, f z ∂(μ 0).prod (Measure.pi μr)))
            ∂(μ 0).prod (Measure.pi μr) := by
        rw [integral_pi_fin_succ μ, hsplit]
      _ ≤ Real.exp (b ^ 2 * t ^ 2 / 8) *
          ∫ r, Real.exp (t * (G r - ∫ p, f p ∂(μ 0).prod (Measure.pi μr)))
            ∂Measure.pi μr := hstep
      _ = Real.exp (b ^ 2 * t ^ 2 / 8) *
          ∫ r, Real.exp (t * (G r - ∫ z, G z ∂Measure.pi μr))
            ∂Measure.pi μr := by rw [hmean]
      _ ≤ Real.exp (b ^ 2 * t ^ 2 / 8) *
          Real.exp ((n : ℝ) * b ^ 2 * t ^ 2 / 8) :=
        mul_le_mul_of_nonneg_left hG (Real.exp_pos _).le
      _ = Real.exp (((n + 1 : ℕ) : ℝ) * b ^ 2 * t ^ 2 / 8) := by
        rw [← Real.exp_add, Nat.cast_add, Nat.cast_one]
        congr 1
        ring

/-- The sharp product MGF gives the actual sub-Gaussian object with proxy
`n * b^2 / 4`. Exponential integrability is obtained from boundedness. -/
theorem hasSubgaussianMGF_centered_pi_sharp {n : ℕ} {E : Fin n → Type*}
    [∀ i, MeasurableSpace (E i)] (μ : ∀ i, Measure (E i))
    [∀ i, IsProbabilityMeasure (μ i)] {F : (∀ i, E i) → ℝ} {M b : ℝ}
    (hM : 0 ≤ M) (hb : 0 ≤ b) (hF : Measurable F)
    (hbound : ∀ x, |F x| ≤ M)
    (hosc : ∀ x i y, |F (Function.update x i y) - F x| ≤ b) :
    HasSubgaussianMGF (fun x => F x - ∫ z, F z ∂Measure.pi μ)
      (⟨(n : ℝ) * b ^ 2 / 4, by positivity⟩ : NNReal)
      (Measure.pi μ) := by
  have hmean : |∫ z, F z ∂Measure.pi μ| ≤ M := by
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
      norm_integral_le_of_norm_le_const (μ := Measure.pi μ) (f := F) (C := M)
        (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hbound x)
  have hcenter : ∀ x, |F x - ∫ z, F z ∂Measure.pi μ| ≤ 2 * M := by
    intro x
    calc
      _ ≤ |F x| + |∫ z, F z ∂Measure.pi μ| := abs_sub _ _
      _ ≤ M + M := add_le_add (hbound x) hmean
      _ = 2 * M := by ring
  refine ⟨?_, ?_⟩
  · intro t
    exact integrable_exp_mul_of_mem_Icc (hF.sub_const _).aemeasurable
      (ae_of_all _ fun x => abs_le.mp (hcenter x))
  · intro t
    change (∫ x, Real.exp (t * (F x - ∫ z, F z ∂Measure.pi μ)) ∂Measure.pi μ) ≤
      Real.exp (((n : ℝ) * b ^ 2 / 4) * t ^ 2 / 2)
    calc
      _ ≤ Real.exp ((n : ℝ) * b ^ 2 * t ^ 2 / 8) :=
        integral_exp_centered_pi_le_sharp μ hM hb hF hbound hosc t
      _ = Real.exp (((n : ℝ) * b ^ 2 / 4) * t ^ 2 / 2) := by
        congr 1
        ring

/-- The sharp one-sided finite-product bound. The positive-scale hypothesis
keeps the displayed decay exponent away from division by zero. -/
theorem measure_ge_centered_pi_le_sharp {n : ℕ} {E : Fin n → Type*}
    [∀ i, MeasurableSpace (E i)] (μ : ∀ i, Measure (E i))
    [∀ i, IsProbabilityMeasure (μ i)] {F : (∀ i, E i) → ℝ} {M b : ℝ}
    (hM : 0 ≤ M) (hb : 0 ≤ b) (hF : Measurable F)
    (hbound : ∀ x, |F x| ≤ M)
    (hosc : ∀ x i y, |F (Function.update x i y) - F x| ≤ b)
    {u : ℝ} (hu : 0 ≤ u) (_hscale : 0 < (n : ℝ) * b ^ 2) :
    (Measure.pi μ).real {x | u ≤ F x - ∫ z, F z ∂Measure.pi μ} ≤
      Real.exp (-(2 * u ^ 2) / ((n : ℝ) * b ^ 2)) := by
  have h := (hasSubgaussianMGF_centered_pi_sharp μ hM hb hF hbound hosc).measure_ge_le hu
  have hexp :
      -u ^ 2 / (2 * ((n : ℝ) * b ^ 2 / 4)) =
        -(2 * u ^ 2) / ((n : ℝ) * b ^ 2) := by
    field_simp [ne_of_gt _hscale]
    ring
  change (Measure.pi μ).real {x | u ≤ F x - ∫ z, F z ∂Measure.pi μ} ≤
    Real.exp (-u ^ 2 / (2 * ((n : ℝ) * b ^ 2 / 4))) at h
  rw [hexp] at h
  exact h

/-- At zero scale, the centered function is zero almost everywhere, so its
nonnegative upper-tail probability is exactly one at threshold zero and zero
at every positive threshold. -/
theorem measure_ge_centered_pi_eq_of_scale_eq_zero
    {n : ℕ} {E : Fin n → Type*} [∀ i, MeasurableSpace (E i)]
    (μ : ∀ i, Measure (E i)) [∀ i, IsProbabilityMeasure (μ i)]
    {F : (∀ i, E i) → ℝ} {M b : ℝ} (hM : 0 ≤ M) (hb : 0 ≤ b)
    (hF : Measurable F) (hbound : ∀ x, |F x| ≤ M)
    (hosc : ∀ x i y, |F (Function.update x i y) - F x| ≤ b)
    (hscale : (n : ℝ) * b ^ 2 = 0) {u : ℝ} (hu : 0 ≤ u) :
    (Measure.pi μ).real {x | u ≤ F x - ∫ z, F z ∂Measure.pi μ} =
      if u = 0 then 1 else 0 := by
  have hmean : |∫ z, F z ∂Measure.pi μ| ≤ M := by
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
      norm_integral_le_of_norm_le_const (μ := Measure.pi μ) (f := F) (C := M)
        (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hbound x)
  have hcenter : ∀ x, |F x - ∫ z, F z ∂Measure.pi μ| ≤ 2 * M := by
    intro x
    calc
      _ ≤ |F x| + |∫ z, F z ∂Measure.pi μ| := abs_sub _ _
      _ ≤ M + M := add_le_add (hbound x) hmean
      _ = 2 * M := by ring
  have hsg0 : HasSubgaussianMGF (fun x => F x - ∫ z, F z ∂Measure.pi μ) 0
      (Measure.pi μ) := by
    refine ⟨?_, ?_⟩
    · intro t
      exact integrable_exp_mul_of_mem_Icc (hF.sub_const _).aemeasurable
        (ae_of_all _ fun x => abs_le.mp (hcenter x))
    · intro t
      change (∫ x, Real.exp (t * (F x - ∫ z, F z ∂Measure.pi μ)) ∂Measure.pi μ) ≤
        Real.exp (0 * t ^ 2 / 2)
      calc
        _ ≤ Real.exp ((n : ℝ) * b ^ 2 * t ^ 2 / 8) :=
          integral_exp_centered_pi_le_sharp μ hM hb hF hbound hosc t
        _ = Real.exp (0 * t ^ 2 / 2) := by
          rw [hscale]
          simp
  have hae := hsg0.ae_eq_zero_of_hasSubgaussianMGF_zero
  have hset : {x | u ≤ F x - ∫ z, F z ∂Measure.pi μ} =ᵐ[Measure.pi μ]
      (if u = 0 then Set.univ else ∅) := by
    filter_upwards [hae] with x hx
    by_cases hu0 : u = 0
    · subst u
      simp [hx]
    · have hu' : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
      simp [hx, hu0, hu']
  calc
    _ = (Measure.pi μ).real (if u = 0 then Set.univ else ∅) := measureReal_congr hset
    _ = if u = 0 then 1 else 0 := by
      by_cases hu0 : u = 0 <;> simp [hu0]

end LPPDifferentiability
