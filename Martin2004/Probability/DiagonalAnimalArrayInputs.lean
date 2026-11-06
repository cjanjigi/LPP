/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.DiagonalAnimalArrayLaw
public import Martin2004.Probability.DiagonalAnimalCenteredMean
public import Martin2004.Probability.DiagonalAnimalConvergence
public import Martin2004.Probability.DiagonalAnimalMean
public import LPP_Foundations.Probability.PassageIntegrable
public import Mathlib.MeasureTheory.MeasurableSpace.MeasurablyGenerated
public import Mathlib.Topology.Order.LiminfLimsup

/-! Inputs on the actual array law of all proper-interval diagonal animal
maxima. Every law below is the literal pushforward of the original environment
law by `diagonalAnimalArray`. -/

@[expose] public section

open MeasureTheory Filter
open Set
open scoped ENNReal Topology

namespace LPPDifferentiability

instance instIsProbabilityMeasureDiagonalAnimalArrayLaw
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure ((environmentLaw μ).map diagonalAnimalArray) := by
  rw [Measure.isProbabilityMeasure_map_iff measurable_diagonalAnimalArray.aemeasurable]
  infer_instance

/-- Every actual proper-interval coordinate has a finite first moment under
the full-array pushforward when the marginal has a finite first moment. -/
theorem integrable_diagonalAnimalArray_eval (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) (a b : ℤ) (hab : a < b) :
    Integrable (fun x : BilateralArray => x ⟨(a, b), hab⟩)
      ((environmentLaw μ).map diagonalAnimalArray) := by
  apply (integrable_map_measure
    (g := fun x : BilateralArray => x ⟨(a, b), hab⟩)
    (f := diagonalAnimalArray)
    (measurable_pi_apply (⟨(a, b), hab⟩ : BilateralInterval)).aestronglyMeasurable
    measurable_diagonalAnimalArray.aemeasurable).2
  change Integrable (fun ω : Environment => diagonalAnimalMaximum a b hab ω)
    (environmentLaw μ)
  apply integrable_diagonalAnimalMaximum (environmentLaw μ) (fun v ω => ω v)
  exact integrable_environment_eval μ hμ

/-- The integral of each full-array coordinate is the integral of the same
actual maximum in the original environment. -/
theorem integral_diagonalAnimalArray_eval (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a b : ℤ) (hab : a < b) :
    (∫ x : BilateralArray, x ⟨(a, b), hab⟩
      ∂((environmentLaw μ).map diagonalAnimalArray)) =
    ∫ ω : Environment, diagonalAnimalMaximum a b hab ω ∂environmentLaw μ := by
  rw [integral_map measurable_diagonalAnimalArray.aemeasurable
    (measurable_pi_apply ⟨(a, b), hab⟩).aestronglyMeasurable]
  rfl

/-- The actual array is simultaneously nonnegative on all proper intervals
almost surely when the source marginal is almost surely nonnegative. -/
theorem ae_diagonalAnimalArray_nonneg (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x) :
    ∀ᵐ x ∂((environmentLaw μ).map diagonalAnimalArray),
      ∀ p : BilateralInterval, 0 ≤ x p := by
  rw [ae_all_iff]
  intro p
  have hsource : ∀ᵐ ω ∂environmentLaw μ, 0 ≤ (diagonalAnimalArray ω) p := by
    filter_upwards [ae_environment_nonneg_of_ae_nonneg μ hμ] with ω hω
    exact diagonalAnimalMaximum_nonneg_of_forall_nonneg
      p.val.1 p.val.2 p.property ω hω
  exact (ae_map_iff measurable_diagonalAnimalArray.aemeasurable
    (measurableSet_le measurable_const (measurable_pi_apply p))).2 hsource

/-- Actual diagonal maxima give a simultaneously superadditive array almost
surely under their full-array law. -/
theorem ae_diagonalAnimalArray_superadditive (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∀ᵐ x ∂((environmentLaw μ).map diagonalAnimalArray),
      ∀ a b c : ℤ, ∀ (hab : a < b) (hbc : b < c),
        x ⟨(a, b), hab⟩ + x ⟨(b, c), hbc⟩ ≤ x ⟨(a, c), lt_trans hab hbc⟩ := by
  have hset : MeasurableSet {x : BilateralArray |
      ∀ a b c : ℤ, ∀ (hab : a < b) (hbc : b < c),
        x ⟨(a, b), hab⟩ + x ⟨(b, c), hbc⟩ ≤ x ⟨(a, c), lt_trans hab hbc⟩} := by
    measurability
  have hsource : ∀ᵐ ω ∂environmentLaw μ,
      ∀ a b c : ℤ, ∀ (hab : a < b) (hbc : b < c),
        (diagonalAnimalArray ω) ⟨(a, b), hab⟩ +
          (diagonalAnimalArray ω) ⟨(b, c), hbc⟩ ≤
            (diagonalAnimalArray ω) ⟨(a, c), lt_trans hab hbc⟩ := by
    filter_upwards with ω
    intro a b c hab hbc
    exact diagonalAnimalMaximum_superadditive hab hbc ω
  exact (ae_map_iff measurable_diagonalAnimalArray.aemeasurable hset).2 hsource

/-- The source nonnegative marginal and positive square-root tail give a
finite real upper bound for every positive origin expected rate under the
actual full-array law. The first moment and mean estimate are derived here
from those source conditions. -/
theorem exists_finite_diagonalAnimalArray_origin_rate_bound
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hnonneg : ∀ᵐ x ∂μ, 0 ≤ x)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ,
      (∫ x : BilateralArray,
        x ⟨(0, ((n + 1 : ℕ) : ℤ)), by omega⟩
          ∂((environmentLaw μ).map diagonalAnimalArray)) /
        ((n + 1 : ℕ) : ℝ) ≤ B := by
  obtain ⟨C, hC, hmean⟩ := exists_positive_diagonalAnimalMaximum_mean_bound
  let T : ℝ≥0∞ := (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ))
  have hμ : Integrable (fun x : ℝ => x) μ := by
    apply (integrable_positivePart_of_positive_sqrt_tail μ hpos).congr
    filter_upwards [hnonneg] with x hx
    exact max_eq_left hx
  have hsource_nonneg := ae_environment_nonneg_of_ae_nonneg μ hnonneg
  refine ⟨C * T.toReal, mul_nonneg hC.le (ENNReal.toReal_nonneg), ?_⟩
  intro n
  have hclip :
      (∫ ω : Environment,
        diagonalAnimalMaximum 0 ((n + 1 : ℕ) : ℤ) (by omega) ω
          ∂environmentLaw μ) =
      ∫ ω : Environment,
        diagonalAnimalMaximum 0 ((n + 1 : ℕ) : ℤ) (by omega)
          (fun v => max (ω v) 0) ∂environmentLaw μ := by
    apply integral_congr_ae
    filter_upwards [hsource_nonneg] with ω hω
    have hfield : (fun v => max (ω v) 0) = ω :=
      funext fun v => max_eq_left (hω v)
    rw [hfield]
  have hb := ((hmean μ (n + 1) (by omega)).2 hpos).2
  have harray := integral_diagonalAnimalArray_eval μ 0
    ((n + 1 : ℕ) : ℤ) (by omega)
  calc
    _ = (∫ ω : Environment,
        diagonalAnimalMaximum 0 ((n + 1 : ℕ) : ℤ) (by omega) ω
          ∂environmentLaw μ) / ((n + 1 : ℕ) : ℝ) := by rw [harray]
    _ = (∫ ω : Environment,
        diagonalAnimalMaximum 0 ((n + 1 : ℕ) : ℤ) (by omega)
          (fun v => max (ω v) 0) ∂environmentLaw μ) / ((n + 1 : ℕ) : ℝ) := by
      rw [hclip]
    _ ≤ (C * ((n + 1 : ℕ) : ℝ) * T.toReal) / ((n + 1 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right hb (by positivity)
    _ = C * T.toReal := by field_simp

/-- Measurability of the extended-real upper limit of the actual centered
proper-interval coordinates on the full-array space. -/
private theorem measurable_diagonalAnimalArray_centered_limsup :
    Measurable (fun x : BilateralArray =>
      limsup (fun n : ℕ =>
        ((x ⟨(-((n + 1 : ℕ) : ℤ), ((n + 1 : ℕ) : ℤ)), by omega⟩ /
          (2 * (n + 1 : ℕ) : ℕ) : ℝ) : EReal)) atTop) := by
  apply Measurable.limsup
  intro n
  have hreal : Measurable (fun x : BilateralArray =>
      x (⟨(-((n + 1 : ℕ) : ℤ), ((n + 1 : ℕ) : ℤ)), by omega⟩ : BilateralInterval) /
        ((2 * (n + 1 : ℕ) : ℕ) : ℝ)) :=
    (measurable_pi_apply
      (⟨(-((n + 1 : ℕ) : ℤ), ((n + 1 : ℕ) : ℤ)), by omega⟩ : BilateralInterval)).div_const _
  exact hreal.coe_real_ereal

/-- Any measurable-array almost-sure upper bound for the centered upper limit
pulls back to the same actual centered upper bound on the environment space.
The event's measurability is proved from its coordinates, not assumed. -/
theorem ae_diagonalAnimalCenteredRate_limsup_le_of_array
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {q : ℝ}
    (hupper : ∀ᵐ x ∂((environmentLaw μ).map diagonalAnimalArray),
      limsup (fun n : ℕ =>
        ((x ⟨(-((n + 1 : ℕ) : ℤ), ((n + 1 : ℕ) : ℤ)), by omega⟩ /
          (2 * (n + 1 : ℕ) : ℕ) : ℝ) : EReal)) atTop ≤ (q : EReal)) :
    ∀ᵐ ω ∂environmentLaw μ,
      limsup (fun n : ℕ => (diagonalAnimalCenteredRate n ω : EReal)) atTop ≤
        (q : EReal) := by
  have hset : MeasurableSet {x : BilateralArray |
      limsup (fun n : ℕ =>
        ((x ⟨(-((n + 1 : ℕ) : ℤ), ((n + 1 : ℕ) : ℤ)), by omega⟩ /
          (2 * (n + 1 : ℕ) : ℕ) : ℝ) : EReal)) atTop ≤ (q : EReal)} :=
    measurableSet_le measurable_diagonalAnimalArray_centered_limsup measurable_const
  rw [ae_map_iff measurable_diagonalAnimalArray.aemeasurable hset] at hupper
  filter_upwards [hupper] with ω hω
  simpa only [diagonalAnimalCenteredRate, diagonalAnimalArray_apply] using hω

/-- Supplied one-sided convergence of the actual maxima transfers to the full
array law. The convergence event is measurable because its coordinates are. -/
theorem ae_diagonalAnimalArray_origin_rate_tendsto_of_environment
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {q : ℝ}
    (hconv : ∀ᵐ ω ∂environmentLaw μ,
      Tendsto (fun n : ℕ =>
        diagonalAnimalMaximum 0 ((n + 1 : ℕ) : ℤ) (by omega) ω /
          ((n + 1 : ℕ) : ℝ)) atTop (𝓝 q)) :
    ∀ᵐ x ∂((environmentLaw μ).map diagonalAnimalArray),
      Tendsto (fun n : ℕ =>
      x ⟨(0, ((n + 1 : ℕ) : ℤ)), by omega⟩ / ((n + 1 : ℕ) : ℝ)) atTop
          (𝓝 q) := by
  have hmeas : ∀ n : ℕ, Measurable (fun x : BilateralArray =>
      x ⟨(0, ((n + 1 : ℕ) : ℤ)), by omega⟩ / ((n + 1 : ℕ) : ℝ)) := by
    intro n
    exact (measurable_pi_apply
      (⟨(0, ((n + 1 : ℕ) : ℤ)), by omega⟩ : BilateralInterval)).div_const _
  have hset : MeasurableSet {x : BilateralArray |
      Tendsto (fun n : ℕ =>
        x ⟨(0, ((n + 1 : ℕ) : ℤ)), by omega⟩ / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 q)} :=
    measurableSet_tendsto (𝓝 q) hmeas
  apply (ae_map_iff measurable_diagonalAnimalArray.aemeasurable hset).2
  filter_upwards [hconv] with ω hω
  simpa only [diagonalAnimalArray_apply] using hω

end LPPDifferentiability
