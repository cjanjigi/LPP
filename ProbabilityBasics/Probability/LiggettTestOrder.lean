/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.IncrementPartialSums
public import ProbabilityBasics.Probability.LiminfOrder
public import Mathlib.Probability.IdentDistrib

/-! # Liggett's joint finite-test comparison

This follows the displayed calculation proving (2.14) of Liggett (1985).
Whole-column laws and origin subadditivity produce the test inequalities;
the weak limit and the liminf extension then consume them.
-/

public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology BoundedContinuousFunction

namespace LPPDifferentiability

private def finiteTest (m : ℕ) (f : (Fin m → ℝ) →ᵇ ℝ) : (ℕ → ℝ) →ᵇ ℝ :=
  f.compContinuous ⟨fun z => fun i => z i.val,
    continuous_pi fun i => continuous_apply i.val⟩

private def partialTest (m : ℕ) (f : (Fin m → ℝ) →ᵇ ℝ) : (ℕ → ℝ) →ᵇ ℝ :=
  (finiteTest m f).compContinuous ⟨sequencePartialSums, continuous_sequencePartialSums⟩

private theorem integrable_origin_test {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : ℕ → ℕ → Ω → ℝ)
    (hm : ∀ j, 0 < j → Measurable (A 0 j)) (m : ℕ) (f : (Fin m → ℝ) →ᵇ ℝ) :
    Integrable (fun ω => f (fun i => A 0 (i.val + 1) ω)) μ :=
  (integrable_const ‖finiteTest m f‖).mono'
    ((finiteTest m f).continuous.measurable.comp
      (measurable_originColumn A hm)).aestronglyMeasurable
    (ae_of_all _ fun ω => (finiteTest m f).norm_coe_le_norm
      (fun k => A 0 (k + 1) ω))

/-- The finite-window increasing-test inequality, before taking the weak limit. -/
theorem integral_partialSums_uniformOriginIncrementLaw_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ℕ → ℕ → Ω → ℝ) (hm : ∀ j, 0 < j → Measurable (A 0 j))
    (hsub : ∀ l n, 0 < l → l < n →
      ∀ᵐ ω ∂μ, A 0 n ω ≤ A 0 l ω + A l n ω)
    (hcol : ∀ l, 0 < l → IdentDistrib
      (fun ω => fun k : ℕ => A l (l + k + 1) ω)
      (fun ω => fun k : ℕ => A 0 (k + 1) ω) μ μ)
    (n m : ℕ) (f : (Fin m → ℝ) →ᵇ ℝ) (hf : Monotone f) :
    (∫ z, f (fun i => sequencePartialSums z i.val)
      ∂(uniformOriginIncrementLaw μ (A 0) hm n : Measure (ℕ → ℝ))) ≤
        ∫ ω, f (fun i => A 0 (i.val + 1) ω) ∂μ := by
  let g := partialTest m f
  change (∫ z, g z ∂_) ≤ _
  rw [integral_uniformOriginIncrementLaw]
  have hcoord (u : Fin (n + 1)) :
      (∫ ω, g (originIncrementSequence (A 0) u.val ω) ∂μ) ≤
        ∫ ω, f (fun i => A 0 (i.val + 1) ω) ∂μ := by
    let l := u.val + 1
    have hl : 0 < l := by dsimp only [l]; omega
    have htest := (hcol l hl).comp (finiteTest m f).continuous.measurable
    have hleft : Integrable (fun ω => g (originIncrementSequence (A 0) u.val ω)) μ :=
      (integrable_const ‖g‖).mono'
        (g.continuous.measurable.comp
          (measurable_originIncrementSequence (A 0) hm u.val)).aestronglyMeasurable
        (ae_of_all _ fun _ω => g.norm_coe_le_norm _)
    have hright := htest.integrable_iff.mpr (integrable_origin_test μ A hm m f)
    calc
      _ ≤ ∫ ω, (finiteTest m f) (fun k => A l (l + k + 1) ω) ∂μ := by
        apply integral_mono_ae hleft hright
        have hall : ∀ᵐ ω ∂μ, ∀ i : Fin m,
            A 0 (l + i.val + 1) ω ≤ A 0 l ω + A l (l + i.val + 1) ω := by
          rw [ae_all_iff]
          intro i
          exact hsub l (l + i.val + 1) hl (by omega)
        filter_upwards [hall] with ω hω
        apply hf
        intro i
        change sequencePartialSums (originIncrementSequence (A 0) u.val ω) i.val ≤
          A l (l + i.val + 1) ω
        rw [sequencePartialSums_originIncrementSequence]
        rw [show i.val + u.val + 2 = l + i.val + 1 by dsimp only [l]; omega]
        change A 0 (l + i.val + 1) ω - A 0 l ω ≤ A l (l + i.val + 1) ω
        exact sub_le_iff_le_add'.mpr (hω i)
      _ = _ := htest.integral_eq
  calc
    _ ≤ (∑ _u : Fin (n + 1), ∫ ω, f (fun i => A 0 (i.val + 1) ω) ∂μ) /
        (n + 1 : ℝ) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum fun u _ => hcoord u) (by positivity)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_add, Nat.cast_one]
      exact mul_div_cancel_left₀ _ (show (n + 1 : ℝ) ≠ 0 by positivity)

/-- Equation (2.14) as explicit finite-coordinate increasing-test integral order
for the cumulative-sum and origin-column probability laws. -/
theorem integral_partialSumsLaw_le_originColumnLaw
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ℕ → ℕ → Ω → ℝ) (hm : ∀ j, 0 < j → Measurable (A 0 j))
    (hsub : ∀ l n, 0 < l → l < n →
      ∀ᵐ ω ∂μ, A 0 n ω ≤ A 0 l ω + A l n ω)
    (hcol : ∀ l, 0 < l → IdentDistrib
      (fun ω => fun k : ℕ => A l (l + k + 1) ω)
      (fun ω => fun k : ℕ => A 0 (k + 1) ω) μ μ)
    (ν : ProbabilityMeasure (ℕ → ℝ)) (r : ℕ → ℕ)
    (hν : Tendsto (fun i => uniformOriginIncrementLaw μ (A 0) hm (r i)) atTop (𝓝 ν))
    (m : ℕ) (f : (Fin m → ℝ) →ᵇ ℝ) (hf : Monotone f) :
    (∫ z, f (fun i => z i.val) ∂(partialSumsLaw ν : Measure (ℕ → ℝ))) ≤
      ∫ z, f (fun i => z i.val) ∂(originColumnLaw μ A hm : Measure (ℕ → ℝ)) := by
  change (∫ z, (finiteTest m f) z ∂_) ≤ ∫ z, (finiteTest m f) z ∂_
  rw [partialSumsLaw_toMeasure, originColumnLaw_toMeasure,
    integral_map continuous_sequencePartialSums.measurable.aemeasurable
      (finiteTest m f).continuous.measurable.aestronglyMeasurable,
    integral_map (measurable_originColumn A hm).aemeasurable
      (finiteTest m f).continuous.measurable.aestronglyMeasurable]
  apply le_of_tendsto
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hν (partialTest m f))
  exact Eventually.of_forall fun i =>
    integral_partialSums_uniformOriginIncrementLaw_le μ A hm hsub hcol (r i) m f hf

/-- The comparison passes to closed normalized lower-limit tails. -/
theorem measure_liminf_partialSums_le_originColumn
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ℕ → ℕ → Ω → ℝ) (hm : ∀ j, 0 < j → Measurable (A 0 j))
    (hsub : ∀ l n, 0 < l → l < n →
      ∀ᵐ ω ∂μ, A 0 n ω ≤ A 0 l ω + A l n ω)
    (hcol : ∀ l, 0 < l → IdentDistrib
      (fun ω => fun k : ℕ => A l (l + k + 1) ω)
      (fun ω => fun k : ℕ => A 0 (k + 1) ω) μ μ)
    (ν : ProbabilityMeasure (ℕ → ℝ)) (r : ℕ → ℕ)
    (hν : Tendsto (fun i => uniformOriginIncrementLaw μ (A 0) hm (r i)) atTop (𝓝 ν))
    (a : ℝ) :
    (partialSumsLaw ν : Measure (ℕ → ℝ)) {z | (a : EReal) ≤
      liminf (fun j => ((z j / (j + 1) : ℝ) : EReal)) atTop} ≤
    (originColumnLaw μ A hm : Measure (ℕ → ℝ)) {z | (a : EReal) ≤
      liminf (fun j => ((z j / (j + 1) : ℝ) : EReal)) atTop} :=
  measure_normalized_liminf_ge_le_of_integral_le _ _
    (fun m f hf => integral_partialSumsLaw_le_originColumnLaw μ A hm hsub hcol ν r hν m f hf) a

end LPPDifferentiability
