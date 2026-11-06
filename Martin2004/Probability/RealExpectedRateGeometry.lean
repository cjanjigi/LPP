/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.MartinRealExpectedRate
public import LPP_Foundations.Analysis.PositiveQuadrantDensity

import Mathlib.Tactic

/-! # Geometry of real expected passage limits

The conditional lemmas below concern a displayed function whose values are
limits of the actual normalized floor expectations. Signed expectations are
corrected by the marginal mean before endpoint comparison. No continuity at
an axis is used and no shape function is selected.
-/

public section

open MeasureTheory Filter Set
open scoped Topology NNReal NNRat ENNReal

namespace LPPDifferentiability

/-- Corrected floor expectations converge to the same displayed rate minus
its signed linear mean. -/
theorem tendsto_corrected_real_floor_rate
    (E : (ℕ × ℕ) → ℝ) (m : ℝ) (g : Quadrant → ℝ)
    (hlim : ∀ x : Quadrant, Tendsto (fun n : ℕ =>
      E (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) / (n : ℝ))
      atTop (𝓝 (g x))) (x : Quadrant) :
    Tendsto (fun n : ℕ =>
      (E (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) -
        ((⌊(n : ℝ) * (x.1 : ℝ)⌋₊ + ⌊(n : ℝ) * (x.2 : ℝ)⌋₊ : ℕ) : ℝ) * m) /
        (n : ℝ)) atTop (𝓝 (g x - ((x.1 : ℝ) + x.2) * m)) := by
  convert (hlim x).sub ((tendsto_floor_pair_length
    (x.1 : ℝ) (x.2 : ℝ) x.1.property x.2.property).mul_const m) using 1
  funext n
  ring

/-- A finite signed mean, corrected by endpoint length, is superadditive at
floored real directions. The at most two omitted sites are accounted for by
the exact length correction, with no sign restriction on the mean. -/
theorem corrected_integral_lastPassage_floor_superadditive
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ) (x y : Quadrant) (n : ℕ) :
    let E := fun z : ℕ × ℕ => ∫ ω : Environment, lastPassage ω 0 z ∂environmentLaw μ
    let m := ∫ t : ℝ, t ∂μ
    let a := (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
    let b := (⌊(n : ℝ) * (y.1 : ℝ)⌋₊, ⌊(n : ℝ) * (y.2 : ℝ)⌋₊)
    let c := (⌊(n : ℝ) * ((x + y).1 : ℝ)⌋₊, ⌊(n : ℝ) * ((x + y).2 : ℝ)⌋₊)
    (E a - ((a.1 + a.2 : ℕ) : ℝ) * m) +
      (E b - ((b.1 + b.2 : ℕ) : ℝ) * m) ≤
      E c - ((c.1 + c.2 : ℕ) : ℝ) * m := by
  dsimp only
  let a := (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
  let b := (⌊(n : ℝ) * (y.1 : ℝ)⌋₊, ⌊(n : ℝ) * (y.2 : ℝ)⌋₊)
  let c := (⌊(n : ℝ) * ((x + y).1 : ℝ)⌋₊, ⌊(n : ℝ) * ((x + y).2 : ℝ)⌋₊)
  have hcoord (s t : ℝ≥0) :
      ⌊(n : ℝ) * (s : ℝ)⌋₊ + ⌊(n : ℝ) * (t : ℝ)⌋₊ ≤
        ⌊(n : ℝ) * ((s + t : ℝ≥0) : ℝ)⌋₊ := by
    apply (Nat.le_floor_iff (by positivity)).mpr
    push_cast
    rw [mul_add]
    exact add_le_add (Nat.floor_le (by positivity)) (Nat.floor_le (by positivity))
  have horder : a + b ≤ c := ⟨hcoord x.1 y.1, hcoord x.2 y.2⟩
  have hs := integral_lastPassage_superadditive μ hμ 0 a b
  have hm := integral_lastPassage_corrected_monotone μ hμ (a + b) c horder.1 horder.2
  have hlen : (((a + b).1 + (a + b).2 : ℕ) : ℝ) =
      ((a.1 + a.2 : ℕ) : ℝ) + ((b.1 + b.2 : ℕ) : ℝ) := by
    simp only [Prod.fst_add, Prod.snd_add, Nat.cast_add]
    ring
  rw [hlen] at hm
  change (_ - ((a.1 + a.2 : ℕ) : ℝ) * _) +
    (_ - ((b.1 + b.2 : ℕ) : ℝ) * _) ≤ _ - ((c.1 + c.2 : ℕ) : ℝ) * _
  linarith only [hs, hm]

/-- Actual expected floor limits inherit superadditivity, including mixed
axis and interior directions. -/
theorem real_expected_rate_superadditive
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ) (g : Quadrant → ℝ)
    (hlim : ∀ x : Quadrant, Tendsto (fun n : ℕ =>
      (∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
        ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (g x))) :
    ∀ x y : Quadrant, g x + g y ≤ g (x + y) := by
  let E := fun z : ℕ × ℕ => ∫ ω : Environment, lastPassage ω 0 z ∂environmentLaw μ
  let m := ∫ t : ℝ, t ∂μ
  have hc := tendsto_corrected_real_floor_rate E m g hlim
  intro x y
  have h := le_of_tendsto_of_tendsto' ((hc x).add (hc y)) (hc (x + y))
    (fun n => by
      simpa only [add_div] using div_le_div_of_nonneg_right
        (corrected_integral_lastPassage_floor_superadditive μ hμ x y n)
        (Nat.cast_nonneg n))
  simp only [Prod.fst_add, Prod.snd_add, NNReal.coe_add] at h
  linarith only [h]

/-- Coordinate exchange preserves the same actual expected rate. -/
theorem real_expected_rate_swap
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ) (g : Quadrant → ℝ)
    (hlim : ∀ x : Quadrant, Tendsto (fun n : ℕ =>
      (∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
        ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (g x))) :
    ∀ x : Quadrant, g x.swap = g x := by
  intro x
  have heq (n : ℕ) :
      (∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.swap.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.swap.2 : ℝ)⌋₊)
        ∂environmentLaw μ) =
      (∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
        ∂environmentLaw μ) := by
    simpa only [Prod.swap_zero, Prod.fst_swap, Prod.snd_swap, Prod.swap_prod_mk] using
      (integrable_and_integral_lastPassage_swap μ hμ 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)).2.2
  have ht := hlim x.swap
  have hs : (fun n : ℕ => (∫ ω : Environment, lastPassage ω 0
      (⌊(n : ℝ) * (x.swap.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.swap.2 : ℝ)⌋₊)
      ∂environmentLaw μ) / (n : ℝ)) =
      (fun n : ℕ => (∫ ω : Environment, lastPassage ω 0
      (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
      ∂environmentLaw μ) / (n : ℝ)) := by
    funext n
    rw [heq n]
  rw [hs] at ht
  exact tendsto_nhds_unique ht (hlim x)

/-- A genuine bounded marginal gives the linear estimate on any displayed
actual expected floor rate, with the same bound constant, including zero. -/
theorem abs_real_expected_rate_le_of_ae_abs_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (L : ℝ) (hL : 0 ≤ L)
    (hμ : ∀ᵐ t ∂μ, |t| ≤ L) (g : Quadrant → ℝ)
    (hlim : ∀ x : Quadrant, Tendsto (fun n : ℕ =>
      (∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
        ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (g x))) :
    ∀ x : Quadrant, |g x| ≤ L * ((x.1 : ℝ) + x.2) := by
  intro x
  have hl := (tendsto_floor_pair_length (x.1 : ℝ) (x.2 : ℝ)
    x.1.property x.2.property).mul_const L
  rw [mul_comm L]
  apply le_of_tendsto_of_tendsto' (hlim x).abs hl
  intro n
  rw [abs_div, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hb := abs_integral_lastPassage_le_of_ae_abs_le μ L hL hμ 0
    (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
  calc
    _ ≤ (((⌊(n : ℝ) * (x.1 : ℝ)⌋₊ + ⌊(n : ℝ) * (x.2 : ℝ)⌋₊ : ℕ) : ℝ) * L) /
        (n : ℝ) := div_le_div_of_nonneg_right hb (Nat.cast_nonneg n)
    _ = _ := by ring

/-- Adjacent integer times transfer a normalized floor limit to every positive
real rescaling. Only corrected endpoint monotonicity is needed. -/
theorem tendsto_real_scaled_floor_of_monotone
    (B : (ℕ × ℕ) → ℝ) (hB : Monotone B) (x : Quadrant)
    (L : ℝ) (hlim : Tendsto (fun n : ℕ =>
      B (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) / (n : ℝ))
      atTop (𝓝 L)) (c : ℝ≥0) (hc : 0 < c) :
    Tendsto (fun n : ℕ =>
      B (⌊(n : ℝ) * ((c • x).1 : ℝ)⌋₊,
        ⌊(n : ℝ) * ((c • x).2 : ℝ)⌋₊) / (n : ℝ))
      atTop (𝓝 ((c : ℝ) * L)) := by
  let k : ℕ → ℕ := fun n => ⌊(n : ℝ) * (c : ℝ)⌋₊
  have hk : Tendsto k atTop atTop := by
    simpa only [k, mul_comm] using tendsto_nat_floor_mul_atTop (c : ℝ) hc
  have hk1 : Tendsto (fun n => k n + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_add_right (k n) 1) hk
  have hr : Tendsto (fun n => (k n : ℝ) / (n : ℝ)) atTop (𝓝 (c : ℝ)) :=
    tendsto_nat_floor_mul_div_nat (c : ℝ) c.property
  have hr1 : Tendsto (fun n => ((k n + 1 : ℕ) : ℝ) / (n : ℝ))
      atTop (𝓝 (c : ℝ)) := by
    simpa only [Nat.cast_add, Nat.cast_one, add_div, add_zero] using
      hr.add (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  have htime (j : ℕ → ℕ) (hj : Tendsto j atTop atTop)
      (hrj : Tendsto (fun n => (j n : ℝ) / (n : ℝ)) atTop (𝓝 (c : ℝ))) :
      Tendsto (fun n => B (⌊(j n : ℝ) * (x.1 : ℝ)⌋₊,
        ⌊(j n : ℝ) * (x.2 : ℝ)⌋₊) / (n : ℝ)) atTop (𝓝 ((c : ℝ) * L)) := by
    apply (hrj.mul (hlim.comp hj)).congr'
    filter_upwards [hj.eventually_gt_atTop 0] with n hn
    dsimp only [Function.comp_def]
    have hj0 : (j n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    field_simp
  have hleft := htime k hk hr
  have hright := htime (fun n => k n + 1) hk1 hr1
  have hcoord (n : ℕ) (t : ℝ≥0) :
      ⌊(k n : ℝ) * (t : ℝ)⌋₊ ≤ ⌊(n : ℝ) * ((c * t : ℝ≥0) : ℝ)⌋₊ ∧
      ⌊(n : ℝ) * ((c * t : ℝ≥0) : ℝ)⌋₊ ≤
        ⌊((k n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ := by
    have hlo : (k n : ℝ) ≤ (n : ℝ) * (c : ℝ) :=
      Nat.floor_le (by positivity)
    have hup : (n : ℝ) * (c : ℝ) ≤ ((k n + 1 : ℕ) : ℝ) := by
      simpa only [k, Nat.cast_add, Nat.cast_one] using
        (Nat.lt_floor_add_one ((n : ℝ) * (c : ℝ))).le
    constructor
    · apply Nat.floor_mono
      change (k n : ℝ) * (t : ℝ) ≤ (n : ℝ) * ((c : ℝ) * (t : ℝ))
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hlo t.property
    · apply Nat.floor_mono
      change (n : ℝ) * ((c : ℝ) * (t : ℝ)) ≤ ((k n + 1 : ℕ) : ℝ) * (t : ℝ)
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hup t.property
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hleft hright
  · exact Eventually.of_forall fun n => div_le_div_of_nonneg_right
      (hB ⟨(hcoord n x.1).1, (hcoord n x.2).1⟩) (Nat.cast_nonneg n)
  · exact Eventually.of_forall fun n => div_le_div_of_nonneg_right
      (hB ⟨(hcoord n x.1).2, (hcoord n x.2).2⟩) (Nat.cast_nonneg n)

/-- Actual zero-displacement passages force the origin value; it is not an
additional hypothesis of the geometry theorems. -/
theorem real_expected_rate_zero
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (g : Quadrant → ℝ)
    (hlim : ∀ x : Quadrant, Tendsto (fun n : ℕ =>
      (∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
        ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (g x))) :
    g 0 = 0 := by
  have ht := hlim 0
  simp only [Prod.fst_zero, Prod.snd_zero, NNReal.coe_zero, mul_zero,
    Nat.floor_zero, lastPassage_zero, integral_zero, zero_div] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

/-- Every actual expected floor rate is homogeneous for all nonnegative real
scalars. Scalar zero is treated directly; positive irrational scalars use
adjacent integer times, without boundary continuity. -/
theorem real_expected_rate_smul
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ) (g : Quadrant → ℝ)
    (hlim : ∀ x : Quadrant, Tendsto (fun n : ℕ =>
      (∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
        ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (g x))) :
    ∀ (c : ℝ≥0) (x : Quadrant), g (c • x) = (c : ℝ) * g x := by
  let E := fun z : ℕ × ℕ => ∫ ω : Environment, lastPassage ω 0 z ∂environmentLaw μ
  let m := ∫ t : ℝ, t ∂μ
  let B := fun z : ℕ × ℕ => E z - ((z.1 + z.2 : ℕ) : ℝ) * m
  have hB : Monotone B := by
    intro z w hzw
    exact integral_lastPassage_corrected_monotone μ hμ z w hzw.1 hzw.2
  have hzero := real_expected_rate_zero μ g hlim
  have hcorr := tendsto_corrected_real_floor_rate E m g hlim
  intro c x
  by_cases hc : c = 0
  · simp only [hc, zero_smul, hzero, NNReal.coe_zero, zero_mul]
  · have hc0 : 0 < c := pos_iff_ne_zero.mpr hc
    have ht := tendsto_real_scaled_floor_of_monotone B hB x
      (g x - ((x.1 : ℝ) + x.2) * m) (hcorr x) c hc0
    have heq := tendsto_nhds_unique (hcorr (c • x)) ht
    change g (c • x) - ((c : ℝ) * (x.1 : ℝ) + (c : ℝ) * (x.2 : ℝ)) * m =
      (c : ℝ) * (g x - ((x.1 : ℝ) + x.2) * m) at heq
    nlinarith only [heq]

/-- Uniqueness identifies the displayed actual real expected rate with any
actual natural expected rate, at the literal casts of natural directions. -/
theorem real_expected_rate_agrees_natural
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (g : Quadrant → ℝ)
    (hlim : ∀ x : Quadrant, Tendsto (fun n : ℕ =>
      (∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
        ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (g x)))
    (r : (ℕ × ℕ) → ℝ)
    (hr : ∀ a : ℕ × ℕ, Tendsto (fun n : ℕ =>
      (∫ ω : Environment, lastPassage ω 0 (n • a) ∂environmentLaw μ) / (n : ℝ))
      atTop (𝓝 (r a))) :
    ∀ a : ℕ × ℕ, g ((a.1 : ℝ≥0), (a.2 : ℝ≥0)) = r a := by
  intro a
  have ht := hlim ((a.1 : ℝ≥0), (a.2 : ℝ≥0))
  have hend (n : ℕ) :
      (⌊(n : ℝ) * (((a.1 : ℝ≥0) : ℝ))⌋₊,
        ⌊(n : ℝ) * (((a.2 : ℝ≥0) : ℝ))⌋₊) = n • a := by
    apply Prod.ext
    · change ⌊(n : ℝ) * (a.1 : ℝ)⌋₊ = n * a.1
      rw [← Nat.cast_mul, Nat.floor_natCast]
    · change ⌊(n : ℝ) * (a.2 : ℝ)⌋₊ = n * a.2
      rw [← Nat.cast_mul, Nat.floor_natCast]
  simp only [hend] at ht
  exact tendsto_nhds_unique ht (hr a)

/-- The unique actual whole-quadrant expected rate has real homogeneity, superadditivity, swap
symmetry and the bounded-law linear estimate. All properties concern the same witness produced by
the real expected-rate theorem; the caller supplies only probability and the two tails. The
conclusion also includes interior continuity, signed axes, the same rational witness and finite
integrability. -/
theorem exists_unique_lastPassage_real_expected_rate_geometry_of_martin_tails
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : (∫⁻ t in Iio (0 : ℝ), (μ (Iic t)) ^ (1 / 2 : ℝ)) < ∞)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞) :
    ∃! g : Quadrant → ℝ,
      ((∀ x : Quadrant, Tendsto (fun n : ℕ =>
        (∫ ω : Environment, lastPassage ω 0
          (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
          ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (g x))) ∧
      Continuous (fun x : QuadrantInterior => g x.val) ∧
      g 0 = 0 ∧
      (∀ s : ℝ≥0, g (s, 0) = (∫ t : ℝ, t ∂μ) * (s : ℝ)) ∧
      (∀ t : ℝ≥0, g (0, t) = (∫ s : ℝ, s ∂μ) * (t : ℝ)) ∧
      (∃ F : (ℚ≥0 × ℚ≥0) → ℝ,
        (∀ q : ℚ≥0 × ℚ≥0, Tendsto (fun n : ℕ =>
          (∫ ω : Environment, lastPassage ω 0
            (⌊(n : ℝ) * (q.1 : ℝ)⌋₊, ⌊(n : ℝ) * (q.2 : ℝ)⌋₊)
            ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (F q))) ∧
        (∀ q : ℚ≥0 × ℚ≥0, g (nnratPairToQuadrant q) = F q)) ∧
      (∀ z : ℕ × ℕ, Integrable (fun ω : Environment => lastPassage ω 0 z)
        (environmentLaw μ))) ∧
      (∀ (c : ℝ≥0) (x : Quadrant), g (c • x) = (c : ℝ) * g x) ∧
      (∀ x y : Quadrant, g x + g y ≤ g (x + y)) ∧
      (∀ x : Quadrant, g x.swap = g x) ∧
      (∀ (L : ℝ), 0 ≤ L → (∀ᵐ t ∂μ, |t| ≤ L) →
        ∀ x : Quadrant, |g x| ≤ L * ((x.1 : ℝ) + x.2)) := by
  obtain ⟨g, hg, hUnique⟩ :=
    exists_unique_lastPassage_real_expected_rate_of_martin_tails μ hneg hpos
  have hμ := integrable_id_of_martin_tails μ hneg hpos
  refine ⟨g, ⟨hg, real_expected_rate_smul μ hμ g hg.1,
    real_expected_rate_superadditive μ hμ g hg.1,
    real_expected_rate_swap μ hμ g hg.1, ?_⟩, ?_⟩
  · intro L hL hbound
    exact abs_real_expected_rate_le_of_ae_abs_le μ L hL hbound g hg.1
  · intro f hf
    exact hUnique f hf.1

end LPPDifferentiability
