/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.SqrtCdfDistance
public import Mathlib.Probability.CentralLimitTheorem
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Moments.Basic
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The square-root distance to the normal law tends to zero (Martin 2004, Lemma 4.5)

Martin (2004), proof of Lemma 4.5, bounds the distance between the distribution function `F~^(r)` of
the normalized sum `(X_1 + ... + X_r - r m) / (σ √r)` and the standard normal one `Φ` by
`C r^(-1/2) (1 + |x|)^(-3)` (a non-uniform Berry-Esseen bound) and integrates the square root to get
`C' r^(-1/4)`. Afterwards only the fact that `∫ |F~^(r)(x) - Φ(x)|^(1/2) dx` tends to `0` is used.
Here the rate is replaced by the central limit theorem: this file proves the qualitative statement
for a law with bounded support and positive variance.

* (CLT) Mathlib's central limit theorem and the portmanteau theorem give `F~^(r)(x) → Φ(x)` at
  every `x`, since `Φ` is continuous.
* (Majorant) The fourth moment of the normalized sum is at most `B^4 + 3` for every `r`, where `B`
  bounds `|X - m| / σ`. Markov's inequality gives a tail bound `C / x^4` for `F~^(r)`, the Chernoff
  bound gives one for `Φ`, so `|F~^(r) - Φ|^(1/2) ≤ c / (1 + x^2)`, an integrable bound.
* (Dominated convergence) The two steps above give the limit.

The distance is the lower integral of `(ENNReal.ofReal |F₁ s - F₂ s|) ^ (1 / 2)`, the form used in
the statements of Lemmas 4.2 and 4.3, with `F s = μ.real (Iic s)`.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal

namespace LPPDifferentiability

/-! ### Fourth moment of a sum of independent centred bounded variables -/

/-- A measurable real function that is almost surely bounded is integrable for a probability
measure. -/
private lemma integrable_of_abs_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {f : Ω → ℝ} (hf : Measurable f) {C : ℝ}
    (h : ∀ᵐ ω ∂P, |f ω| ≤ C) : Integrable f P :=
  Integrable.of_bound hf.aestronglyMeasurable C (h.mono fun ω hω => by rwa [Real.norm_eq_abs])

/-- A sum of `r` variables bounded by `B` is bounded by `r * B`. -/
private lemma abs_sum_le_of_bound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : ℕ → Ω → ℝ} {B : ℝ} (hB : ∀ k, ∀ᵐ ω ∂P, |Y k ω| ≤ B) (r : ℕ) :
    ∀ᵐ ω ∂P, |∑ k ∈ Finset.range r, Y k ω| ≤ r * B := by
  filter_upwards [ae_all_iff.2 hB] with ω hω
  calc |∑ k ∈ Finset.range r, Y k ω| ≤ ∑ k ∈ Finset.range r, |Y k ω| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range r, B := Finset.sum_le_sum fun k _ => hω k
    _ = r * B := by simp

/-- One step of the moment recursion. Adding to a centred variable `S` (bounded by `T`) an
independent centred variable `Y` of variance one (bounded by `B`) adds `1` to the second moment and
at most `6 E S^2 + B^4` to the fourth moment: the cross terms `E S^3 E Y`, `E S E Y^3` vanish. -/
private lemma moments_step {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {S Y : Ω → ℝ} (hS : Measurable S) (hY : Measurable Y)
    (hind : IndepFun S Y P) {T B : ℝ} (hT : ∀ᵐ ω ∂P, |S ω| ≤ T) (hB : ∀ᵐ ω ∂P, |Y ω| ≤ B)
    (hS0 : ∫ ω, S ω ∂P = 0) (hY0 : ∫ ω, Y ω ∂P = 0) (hY2 : ∫ ω, Y ω ^ 2 ∂P = 1) :
    (∫ ω, (S ω + Y ω) ^ 2 ∂P = ∫ ω, S ω ^ 2 ∂P + 1) ∧
      ∫ ω, (S ω + Y ω) ^ 4 ∂P ≤ ∫ ω, S ω ^ 4 ∂P + 6 * ∫ ω, S ω ^ 2 ∂P + B ^ 4 := by
  -- every product `S ^ a * Y ^ b` is integrable, since both factors are bounded
  have hint : ∀ a b : ℕ, Integrable (fun ω => S ω ^ a * Y ω ^ b) P := by
    intro a b
    refine integrable_of_abs_le ((hS.pow_const a).mul (hY.pow_const b)) (C := T ^ a * B ^ b) ?_
    filter_upwards [hT, hB] with ω h1 h2
    rw [abs_mul, abs_pow, abs_pow]
    exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) h1 a) (pow_le_pow_left₀ (abs_nonneg _) h2 b)
      (pow_nonneg (abs_nonneg _) b) (pow_nonneg ((abs_nonneg _).trans h1) a)
  -- independence of the powers: `E[S^a Y^b] = E[S^a] E[Y^b]`
  have hmul : ∀ a b : ℕ,
      ∫ ω, S ω ^ a * Y ω ^ b ∂P = (∫ ω, S ω ^ a ∂P) * ∫ ω, Y ω ^ b ∂P := by
    intro a b
    exact (hind.comp (measurable_id.pow_const a) (measurable_id.pow_const b)).integral_fun_mul_eq_mul_integral
      (hS.pow_const a).aestronglyMeasurable (hY.pow_const b).aestronglyMeasurable
  have hS1 : ∫ ω, S ω ^ 1 ∂P = 0 := by simpa using hS0
  have hY1 : ∫ ω, Y ω ^ 1 ∂P = 0 := by simpa using hY0
  refine ⟨?_, ?_⟩
  · -- the second moment
    have e : ∀ ω, (S ω + Y ω) ^ 2 = S ω ^ 2 + 2 * (S ω ^ 1 * Y ω ^ 1) + Y ω ^ 2 :=
      fun ω => by ring
    have i1 : Integrable (fun ω => S ω ^ 2) P := by simpa using hint 2 0
    have i2 : Integrable (fun ω => S ω ^ 1 * Y ω ^ 1) P := hint 1 1
    have i3 : Integrable (fun ω => Y ω ^ 2) P := by simpa using hint 0 2
    have j2 : Integrable (fun ω => S ω ^ 2 + 2 * (S ω ^ 1 * Y ω ^ 1)) P :=
      i1.add (i2.const_mul 2)
    simp_rw [e]
    rw [integral_add j2 i3, integral_add i1 (i2.const_mul 2), integral_const_mul, hmul 1 1, hS1,
      hY2]
    simp only [zero_mul, mul_zero, add_zero]
  · -- the fourth moment
    have e : ∀ ω, (S ω + Y ω) ^ 4 = S ω ^ 4 + 4 * (S ω ^ 3 * Y ω ^ 1) + 6 * (S ω ^ 2 * Y ω ^ 2)
        + 4 * (S ω ^ 1 * Y ω ^ 3) + Y ω ^ 4 := fun ω => by ring
    have i1 : Integrable (fun ω => S ω ^ 4) P := by simpa using hint 4 0
    have i2 : Integrable (fun ω => S ω ^ 3 * Y ω ^ 1) P := hint 3 1
    have i3 : Integrable (fun ω => S ω ^ 2 * Y ω ^ 2) P := hint 2 2
    have i4 : Integrable (fun ω => S ω ^ 1 * Y ω ^ 3) P := hint 1 3
    have i5 : Integrable (fun ω => Y ω ^ 4) P := by simpa using hint 0 4
    have j2 : Integrable (fun ω => S ω ^ 4 + 4 * (S ω ^ 3 * Y ω ^ 1)) P :=
      i1.add (i2.const_mul 4)
    have j3 : Integrable
        (fun ω => S ω ^ 4 + 4 * (S ω ^ 3 * Y ω ^ 1) + 6 * (S ω ^ 2 * Y ω ^ 2)) P :=
      j2.add (i3.const_mul 6)
    have j4 : Integrable (fun ω => S ω ^ 4 + 4 * (S ω ^ 3 * Y ω ^ 1) +
        6 * (S ω ^ 2 * Y ω ^ 2) + 4 * (S ω ^ 1 * Y ω ^ 3)) P :=
      j3.add (i4.const_mul 4)
    have hY4 : ∫ ω, Y ω ^ 4 ∂P ≤ B ^ 4 := by
      calc ∫ ω, Y ω ^ 4 ∂P ≤ ∫ _ω, B ^ 4 ∂P := by
            refine integral_mono_ae i5 (integrable_const _) ?_
            filter_upwards [hB] with ω h
            calc Y ω ^ 4 = |Y ω| ^ 4 := (Even.pow_abs (by decide) _).symm
              _ ≤ B ^ 4 := pow_le_pow_left₀ (abs_nonneg _) h 4
        _ = B ^ 4 := by simp
    simp_rw [e]
    rw [integral_add j4 i5, integral_add j3 (i4.const_mul 4), integral_add j2 (i3.const_mul 6),
      integral_add i1 (i2.const_mul 4), integral_const_mul, integral_const_mul, integral_const_mul,
      hmul 3 1, hmul 2 2, hmul 1 3, hY1, hS1, hY2]
    simp only [mul_zero, zero_mul, add_zero, mul_one]
    linarith

/-- Moments of the partial sums `Y 0 + ... + Y (r - 1)` of independent centred variables of variance
one that are bounded by `B`: the mean is `0`, the second moment is `r`, and the fourth moment is at
most `r B^4 + 3 r^2` (the expansion `r E Y^4 + 3 r (r - 1)`, with the fourth moment of each term
bounded by `B^4`). -/
private lemma partial_sum_moments {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : ℕ → Ω → ℝ} (hmeas : ∀ k, Measurable (Y k))
    (hind : iIndepFun Y P) {B : ℝ} (hB : ∀ k, ∀ᵐ ω ∂P, |Y k ω| ≤ B)
    (h0 : ∀ k, ∫ ω, Y k ω ∂P = 0) (h2 : ∀ k, ∫ ω, Y k ω ^ 2 ∂P = 1) (r : ℕ) :
    (∫ ω, ∑ k ∈ Finset.range r, Y k ω ∂P) = 0 ∧
      (∫ ω, (∑ k ∈ Finset.range r, Y k ω) ^ 2 ∂P) = r ∧
      ∫ ω, (∑ k ∈ Finset.range r, Y k ω) ^ 4 ∂P ≤ r * B ^ 4 + 3 * r ^ 2 := by
  induction r with
  | zero => simp
  | succ r ih =>
    obtain ⟨ih0, ih2, ih4⟩ := ih
    have hS : Measurable fun ω => ∑ k ∈ Finset.range r, Y k ω :=
      Finset.measurable_sum _ fun k _ => hmeas k
    have hindep : IndepFun (fun ω => ∑ k ∈ Finset.range r, Y k ω) (Y r) P := by
      have h := hind.indepFun_finsetSum_of_notMem hmeas (Finset.notMem_range_self (n := r))
      have e : (∑ j ∈ Finset.range r, Y j) = fun ω => ∑ j ∈ Finset.range r, Y j ω :=
        funext fun ω => Finset.sum_apply ω _ _
      rwa [e] at h
    obtain ⟨step2, step4⟩ := moments_step hS (hmeas r) hindep (abs_sum_le_of_bound hB r) (hB r)
      ih0 (h0 r) (h2 r)
    refine ⟨?_, ?_, ?_⟩
    · calc ∫ ω, ∑ k ∈ Finset.range (r + 1), Y k ω ∂P
          = ∫ ω, (∑ k ∈ Finset.range r, Y k ω + Y r ω) ∂P := by simp_rw [Finset.sum_range_succ]
        _ = 0 := by
          rw [integral_add (integrable_of_abs_le hS (abs_sum_le_of_bound hB r))
            (integrable_of_abs_le (hmeas r) (hB r)), ih0, h0 r, add_zero]
    · calc ∫ ω, (∑ k ∈ Finset.range (r + 1), Y k ω) ^ 2 ∂P
          = ∫ ω, (∑ k ∈ Finset.range r, Y k ω + Y r ω) ^ 2 ∂P := by
            simp_rw [Finset.sum_range_succ]
        _ = ((r + 1 : ℕ) : ℝ) := by rw [step2, ih2]; push_cast; ring
    · calc ∫ ω, (∑ k ∈ Finset.range (r + 1), Y k ω) ^ 4 ∂P
          = ∫ ω, (∑ k ∈ Finset.range r, Y k ω + Y r ω) ^ 4 ∂P := by
            simp_rw [Finset.sum_range_succ]
        _ ≤ _ := step4
        _ ≤ ((r + 1 : ℕ) : ℝ) * B ^ 4 + 3 * ((r + 1 : ℕ) : ℝ) ^ 2 := by
          rw [ih2]; push_cast; linarith [ih4]

/-- The fourth moment of the normalized sum `S_r / √r` is at most `B^4 + 3` for every `r` (the
uniform fourth-moment bound of the majorant step). -/
private lemma fourth_moment_normalized {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : ℕ → Ω → ℝ} (hmeas : ∀ k, Measurable (Y k))
    (hind : iIndepFun Y P) {B : ℝ} (hB : ∀ k, ∀ᵐ ω ∂P, |Y k ω| ≤ B)
    (h0 : ∀ k, ∫ ω, Y k ω ∂P = 0) (h2 : ∀ k, ∫ ω, Y k ω ^ 2 ∂P = 1) (r : ℕ) :
    ∫ ω, ((Real.sqrt (r : ℝ))⁻¹ * ∑ k ∈ Finset.range r, Y k ω) ^ 4 ∂P ≤ B ^ 4 + 3 := by
  obtain ⟨-, -, h4⟩ := partial_sum_moments hmeas hind hB h0 h2 r
  have hB4 : 0 ≤ B ^ 4 := by positivity
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · refine le_trans (le_of_eq ?_) (by positivity : (0 : ℝ) ≤ B ^ 4 + 3)
    simp
  · have hrpos : (0 : ℝ) < r := Nat.cast_pos.2 hr
    have hr1 : (1 : ℝ) ≤ r := Nat.one_le_cast.2 hr
    have hsqrt : Real.sqrt (r : ℝ) ^ 4 = (r : ℝ) ^ 2 := by
      have := Real.sq_sqrt hrpos.le
      calc Real.sqrt (r : ℝ) ^ 4 = (Real.sqrt (r : ℝ) ^ 2) ^ 2 := by ring
        _ = (r : ℝ) ^ 2 := by rw [this]
    have e : ∀ ω, ((Real.sqrt (r : ℝ))⁻¹ * ∑ k ∈ Finset.range r, Y k ω) ^ 4 =
        ((r : ℝ) ^ 2)⁻¹ * (∑ k ∈ Finset.range r, Y k ω) ^ 4 := fun ω => by
      rw [mul_pow, inv_pow, hsqrt]
    simp_rw [e]
    rw [integral_const_mul]
    calc ((r : ℝ) ^ 2)⁻¹ * ∫ ω, (∑ k ∈ Finset.range r, Y k ω) ^ 4 ∂P
        ≤ ((r : ℝ) ^ 2)⁻¹ * (r * B ^ 4 + 3 * r ^ 2) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ ≤ B ^ 4 + 3 := by
          rw [inv_mul_le_iff₀ (by positivity)]
          have hrr : (r : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith
          have := mul_le_mul_of_nonneg_right hrr hB4
          nlinarith

/-! ### Tail bounds -/

/-- Markov's inequality for the fourth power: both tails at distance `t` from the origin have
mass at most `C / t^4` when the fourth moment is at most `C`. -/
private lemma markov_fourth {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hint : Integrable (fun z : ℝ => z ^ 4) ν) {C : ℝ} (hC : ∫ z : ℝ, z ^ 4 ∂ν ≤ C) {t : ℝ}
    (ht : 0 < t) : ν.real (Ici t) ≤ C / t ^ 4 ∧ ν.real (Iic (-t)) ≤ C / t ^ 4 := by
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := ν) (f := fun z : ℝ => z ^ 4)
    (ae_of_all _ fun z => show (0 : ℝ) ≤ z ^ 4 by positivity) hint (t ^ 4)
  have ht4 : 0 < t ^ 4 := pow_pos ht 4
  have key : ν.real {z | t ^ 4 ≤ z ^ 4} ≤ C / t ^ 4 := by
    rw [le_div_iff₀ ht4, mul_comm]
    exact hmark.trans hC
  constructor
  · refine le_trans (measureReal_mono ?_) key
    intro z hz
    exact pow_le_pow_left₀ ht.le hz 4
  · refine le_trans (measureReal_mono ?_) key
    intro z hz
    have hz' : t ≤ -z := by linarith [mem_Iic.1 hz]
    calc t ^ 4 ≤ (-z) ^ 4 := pow_le_pow_left₀ ht.le hz' 4
      _ = z ^ 4 := by ring

/-- Tail bounds for the law of the normalized sum `S_r / √r`, uniform in `r` (the majorant step). -/
private lemma normalized_tail {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : ℕ → Ω → ℝ} (hmeas : ∀ k, Measurable (Y k))
    (hind : iIndepFun Y P) {B : ℝ} (hB : ∀ k, ∀ᵐ ω ∂P, |Y k ω| ≤ B)
    (h0 : ∀ k, ∫ ω, Y k ω ∂P = 0) (h2 : ∀ k, ∫ ω, Y k ω ^ 2 ∂P = 1) (r : ℕ) {t : ℝ}
    (ht : 0 < t) :
    (P.map fun ω => (Real.sqrt (r : ℝ))⁻¹ * ∑ k ∈ Finset.range r, Y k ω).real (Ici t) ≤
        (B ^ 4 + 3) / t ^ 4 ∧
      (P.map fun ω => (Real.sqrt (r : ℝ))⁻¹ * ∑ k ∈ Finset.range r, Y k ω).real (Iic (-t)) ≤
        (B ^ 4 + 3) / t ^ 4 := by
  have hZ : Measurable fun ω => (Real.sqrt (r : ℝ))⁻¹ * ∑ k ∈ Finset.range r, Y k ω :=
    (Finset.measurable_sum _ fun k _ => hmeas k).const_mul _
  have hZ4 : Integrable (fun ω => ((Real.sqrt (r : ℝ))⁻¹ * ∑ k ∈ Finset.range r, Y k ω) ^ 4) P := by
    refine integrable_of_abs_le (hZ.pow_const 4) (C := ((Real.sqrt (r : ℝ))⁻¹ * (r * B)) ^ 4) ?_
    filter_upwards [abs_sum_le_of_bound hB r] with ω h
    rw [abs_pow]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ 4
    rw [abs_mul, abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
    exact mul_le_mul_of_nonneg_left h (inv_nonneg.2 (Real.sqrt_nonneg _))
  have h4m : Measurable fun z : ℝ => z ^ 4 := measurable_id.pow_const 4
  have hint : Integrable (fun z : ℝ => z ^ 4)
      (P.map fun ω => (Real.sqrt (r : ℝ))⁻¹ * ∑ k ∈ Finset.range r, Y k ω) :=
    (integrable_map_measure h4m.aestronglyMeasurable hZ.aemeasurable).2 hZ4
  have hmom : ∫ z : ℝ, z ^ 4 ∂(P.map fun ω => (Real.sqrt (r : ℝ))⁻¹ * ∑ k ∈ Finset.range r, Y k ω)
      ≤ B ^ 4 + 3 := by
    rw [integral_map hZ.aemeasurable h4m.aestronglyMeasurable]
    exact fourth_moment_normalized hmeas hind hB h0 h2 r
  exact markov_fourth hint hmom ht

/-- `exp (-t^2/2) ≤ 8 / t^4`, from `exp u ≥ u^2 / 2`. -/
private lemma exp_neg_half_sq_le {t : ℝ} (ht : 0 < t) : Real.exp (-(t ^ 2) / 2) ≤ 8 / t ^ 4 := by
  have h := Real.quadratic_le_exp_of_nonneg (show 0 ≤ t ^ 2 / 2 by positivity)
  have hpos : 0 < Real.exp (t ^ 2 / 2) := Real.exp_pos _
  have e : Real.exp (-(t ^ 2) / 2) = 1 / Real.exp (t ^ 2 / 2) := by
    rw [one_div, ← Real.exp_neg]; congr 1; ring
  rw [e, div_le_div_iff₀ hpos (pow_pos ht 4)]
  nlinarith [sq_nonneg t]

/-- Both tails of the standard normal law at distance `t` have mass at most `8 / t^4`
(Chernoff bound with the moment generating function `exp (s^2 / 2)`, then `exp_neg_half_sq_le`). -/
private lemma gaussian_tail {t : ℝ} (ht : 0 < t) :
    (gaussianReal 0 1).real (Ici t) ≤ 8 / t ^ 4 ∧ (gaussianReal 0 1).real (Iic (-t)) ≤ 8 / t ^ 4 := by
  have hmgf : ∀ s : ℝ, mgf id (gaussianReal 0 1) s = Real.exp (s ^ 2 / 2) := fun s => by
    rw [mgf_id_gaussianReal]; simp
  have hup := measure_ge_le_exp_mul_mgf (μ := gaussianReal 0 1) (X := id) (t := t) t ht.le
    (integrable_exp_mul_gaussianReal t)
  have hlo := measure_le_le_exp_mul_mgf (μ := gaussianReal 0 1) (X := id) (t := -t) (-t)
    (neg_nonpos.2 ht.le) (integrable_exp_mul_gaussianReal (-t))
  rw [hmgf, ← Real.exp_add, show -t * t + t ^ 2 / 2 = -(t ^ 2) / 2 by ring] at hup
  rw [hmgf, ← Real.exp_add, show -(-t) * -t + (-t) ^ 2 / 2 = -(t ^ 2) / 2 by ring] at hlo
  exact ⟨hup.trans (exp_neg_half_sq_le ht), hlo.trans (exp_neg_half_sq_le ht)⟩

/-- Enlarging the constant in a tail bound. -/
private lemma div_pow_mono {a b t : ℝ} (ht : 0 < t) (hab : a ≤ b) : a / t ^ 4 ≤ b / t ^ 4 :=
  (div_le_div_iff_of_pos_right (pow_pos ht 4)).2 hab

/-! ### From tail bounds and pointwise convergence to the square-root distance -/

/-- A distribution function is one minus the upper tail. -/
private lemma real_Iic_eq (ν : Measure ℝ) [IsProbabilityMeasure ν] (x : ℝ) :
    ν.real (Iic x) = 1 - ν.real (Ioi x) := by
  have h := measureReal_compl (μ := ν) (measurableSet_Iic (a := x))
  rw [compl_Iic, probReal_univ] at h
  linarith

/-- Two distribution functions differ by at most one. -/
private lemma abs_cdf_sub_le_one (ρ γ : Measure ℝ) [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure γ] (x : ℝ) : |ρ.real (Iic x) - γ.real (Iic x)| ≤ 1 := by
  have h1 := measureReal_nonneg (μ := ρ) (s := Iic x)
  have h2 := measureReal_nonneg (μ := γ) (s := Iic x)
  have h3 := measureReal_le_one (μ := ρ) (s := Iic x)
  have h4 := measureReal_le_one (μ := γ) (s := Iic x)
  rw [abs_le]
  constructor <;> linarith

/-- If both laws have tails at most `A / t^4` at distance `t`, their distribution functions differ
by at most `2 A / x^4` at every `x ≠ 0` (the bound in Martin's proof, with a power tail in place of
the Berry-Esseen bound). -/
private lemma abs_cdf_sub_le (ρ γ : Measure ℝ) [IsProbabilityMeasure ρ] [IsProbabilityMeasure γ]
    {A : ℝ}
    (hρ : ∀ t : ℝ, 0 < t → ρ.real (Ici t) ≤ A / t ^ 4 ∧ ρ.real (Iic (-t)) ≤ A / t ^ 4)
    (hγ : ∀ t : ℝ, 0 < t → γ.real (Ici t) ≤ A / t ^ 4 ∧ γ.real (Iic (-t)) ≤ A / t ^ 4)
    {x : ℝ} (hx : x ≠ 0) : |ρ.real (Iic x) - γ.real (Iic x)| ≤ 2 * A / x ^ 4 := by
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · have a1 : ρ.real (Iic x) ≤ A / x ^ 4 := by
      have h := (hρ (-x) (neg_pos.2 hneg)).2
      rwa [neg_neg, show (-x) ^ 4 = x ^ 4 by ring] at h
    have a2 : γ.real (Iic x) ≤ A / x ^ 4 := by
      have h := (hγ (-x) (neg_pos.2 hneg)).2
      rwa [neg_neg, show (-x) ^ 4 = x ^ 4 by ring] at h
    have n1 := measureReal_nonneg (μ := ρ) (s := Iic x)
    have n2 := measureReal_nonneg (μ := γ) (s := Iic x)
    calc |ρ.real (Iic x) - γ.real (Iic x)| ≤ ρ.real (Iic x) + γ.real (Iic x) := by
          rw [abs_le]; constructor <;> linarith
      _ ≤ A / x ^ 4 + A / x ^ 4 := add_le_add a1 a2
      _ = 2 * A / x ^ 4 := by ring
  · have a1 : ρ.real (Ioi x) ≤ A / x ^ 4 :=
      le_trans (measureReal_mono Ioi_subset_Ici_self) (hρ x hpos).1
    have a2 : γ.real (Ioi x) ≤ A / x ^ 4 :=
      le_trans (measureReal_mono Ioi_subset_Ici_self) (hγ x hpos).1
    have n1 := measureReal_nonneg (μ := ρ) (s := Ioi x)
    have n2 := measureReal_nonneg (μ := γ) (s := Ioi x)
    rw [real_Iic_eq ρ x, real_Iic_eq γ x]
    calc |1 - ρ.real (Ioi x) - (1 - γ.real (Ioi x))| ≤ ρ.real (Ioi x) + γ.real (Ioi x) := by
          rw [abs_le]; constructor <;> linarith
      _ ≤ A / x ^ 4 + A / x ^ 4 := add_le_add a1 a2
      _ = 2 * A / x ^ 4 := by ring

/-- The square root of a number `d` with `|d| ≤ 1` and `|d| ≤ A / x^4` is at most
`2 (1 + √A) / (1 + x^2)` (the integrable majorant that replaces the integral of `(1 + |x|)^(-3/2)`
in Martin's proof). -/
private lemma rpow_half_abs_le {d x A : ℝ} (hA : 0 ≤ A) (h1 : |d| ≤ 1)
    (h4 : x ≠ 0 → |d| ≤ A / x ^ 4) :
    |d| ^ (1 / 2 : ℝ) ≤ 2 * (1 + Real.sqrt A) / (1 + x ^ 2) := by
  have hsq := Real.sqrt_nonneg A
  rcases lt_or_ge (x ^ 2) 1 with hx | hx
  · calc |d| ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one (abs_nonneg _) h1 (by norm_num)
      _ ≤ 2 * (1 + Real.sqrt A) / (1 + x ^ 2) := by
          rw [le_div_iff₀ (by positivity)]
          linarith
  · have hx0 : x ≠ 0 := by
      rintro rfl
      norm_num at hx
    have hx2 : 0 < x ^ 2 := by linarith
    calc |d| ^ (1 / 2 : ℝ) = Real.sqrt |d| := (Real.sqrt_eq_rpow _).symm
      _ ≤ Real.sqrt A / x ^ 2 := by
          rw [Real.sqrt_le_iff]
          refine ⟨by positivity, ?_⟩
          rw [div_pow, Real.sq_sqrt hA, show (x ^ 2) ^ 2 = x ^ 4 by ring]
          exact h4 hx0
      _ ≤ 2 * (1 + Real.sqrt A) / (1 + x ^ 2) := by
          rw [div_le_div_iff₀ hx2 (by positivity)]
          nlinarith [mul_nonneg hsq (sub_nonneg.2 hx)]

/-- A distribution function is measurable in the level. -/
private lemma measurable_real_Iic (ν : Measure ℝ) [IsFiniteMeasure ν] :
    Measurable fun x : ℝ => ν.real (Iic x) :=
  Monotone.measurable fun _ _ hab => measureReal_mono (Iic_subset_Iic.2 hab)

/-- The majorant `c / (1 + x^2)` has finite lower integral. -/
private lemma lintegral_majorant_ne_top (c : ℝ) (hc : 0 ≤ c) :
    ∫⁻ x : ℝ, ENNReal.ofReal (c * (1 + x ^ 2)⁻¹) ≠ ∞ := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_inv_one_add_sq.const_mul c)
    (Eventually.of_forall fun x => mul_nonneg hc (inv_nonneg.2 (by positivity)))]
  exact ENNReal.ofReal_ne_top

/-- The dominated convergence step: if the laws `ρ r` converge to `γ` pointwise in distribution
function, and all have tails at most `A / t^4`, then the square-root distance tends to zero, by
dominated convergence with the majorant `2 (1 + √(2 A)) / (1 + x^2)`. -/
private lemma sqrt_distance_tendsto {ρ : ℕ → Measure ℝ} [∀ r, IsProbabilityMeasure (ρ r)]
    {γ : Measure ℝ} [IsProbabilityMeasure γ] {A : ℝ} (hA : 0 ≤ A)
    (hρ : ∀ (r : ℕ) (t : ℝ), 0 < t →
      (ρ r).real (Ici t) ≤ A / t ^ 4 ∧ (ρ r).real (Iic (-t)) ≤ A / t ^ 4)
    (hγ : ∀ t : ℝ, 0 < t → γ.real (Ici t) ≤ A / t ^ 4 ∧ γ.real (Iic (-t)) ≤ A / t ^ 4)
    (hconv : ∀ x : ℝ, Tendsto (fun r : ℕ => (ρ r).real (Iic x)) atTop (𝓝 (γ.real (Iic x)))) :
    Tendsto (fun r : ℕ => sqrtCdfDistance (ρ r) γ) atTop (𝓝 0) := by
  have hbound : ∀ (r : ℕ) (x : ℝ),
      (ENNReal.ofReal |(ρ r).real (Iic x) - γ.real (Iic x)|) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (2 * (1 + Real.sqrt (2 * A)) * (1 + x ^ 2)⁻¹) := by
    intro r x
    rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← div_eq_mul_inv]
    exact rpow_half_abs_le (by positivity) (abs_cdf_sub_le_one (ρ r) γ x)
      fun hx => abs_cdf_sub_le (ρ r) γ (hρ r) hγ hx
  have hlim : ∀ x : ℝ, Tendsto (fun r : ℕ =>
      (ENNReal.ofReal |(ρ r).real (Iic x) - γ.real (Iic x)|) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
    intro x
    have h1 : Tendsto (fun r : ℕ => (ρ r).real (Iic x) - γ.real (Iic x)) atTop (𝓝 0) := by
      have h := (hconv x).sub_const (γ.real (Iic x))
      rwa [sub_self] at h
    have hcont : Continuous fun z : ℝ => (ENNReal.ofReal |z|) ^ (1 / 2 : ℝ) :=
      ENNReal.continuous_rpow_const.comp (ENNReal.continuous_ofReal.comp continuous_abs)
    have h2 : Tendsto (fun r : ℕ =>
        (ENNReal.ofReal |(ρ r).real (Iic x) - γ.real (Iic x)|) ^ (1 / 2 : ℝ)) atTop
        (𝓝 ((ENNReal.ofReal |(0 : ℝ)|) ^ (1 / 2 : ℝ))) := (hcont.tendsto 0).comp h1
    rwa [abs_zero, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      at h2
  have hdom := tendsto_lintegral_of_dominated_convergence (μ := volume)
    (F := fun (r : ℕ) (x : ℝ) =>
      (ENNReal.ofReal |(ρ r).real (Iic x) - γ.real (Iic x)|) ^ (1 / 2 : ℝ))
    (f := fun _ : ℝ => (0 : ℝ≥0∞))
    (fun x => ENNReal.ofReal (2 * (1 + Real.sqrt (2 * A)) * (1 + x ^ 2)⁻¹))
    (fun r => (ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp
      ((measurable_real_Iic (ρ r)).sub (measurable_real_Iic γ)))).pow_const (1 / 2 : ℝ))
    (fun r => Eventually.of_forall (hbound r))
    (lintegral_majorant_ne_top _ (by positivity)) (Eventually.of_forall hlim)
  rwa [lintegral_zero] at hdom

/-! ### The independent copies and the central limit theorem -/

/-- Evaluation at a coordinate is measurable. -/
private lemma measurable_eval (k : ℕ) : Measurable fun ω : ℕ → ℝ => ω k := measurable_pi_apply k

/-- The first `r` coordinates of the infinite product law form the finite product law. -/
private lemma map_restrict_eq_pi (μ : Measure ℝ) [IsProbabilityMeasure μ] (r : ℕ) :
    (Measure.infinitePi fun _ : ℕ => μ).map (fun (ω : ℕ → ℝ) (i : Fin r) => ω i) =
      Measure.pi fun _ : Fin r => μ := by
  have hind : iIndepFun (fun (i : Fin r) (ω : ℕ → ℝ) => ω i)
      (Measure.infinitePi fun _ : ℕ => μ) :=
    (iIndepFun_infinitePi (P := fun _ : ℕ => μ) (X := fun _ t => t)
      (fun _ => measurable_id)).precomp Fin.val_injective
  have hmap := (iIndepFun_iff_map_fun_eq_pi_map (f := fun (i : Fin r) (ω : ℕ → ℝ) => ω i)
    fun i => (measurable_eval (i : ℕ)).aemeasurable).1 hind
  rw [hmap]
  congr 1
  funext i
  exact Measure.infinitePi_map_eval (fun _ : ℕ => μ) i

/-- The law of the normalized sum on the finite product is that of the normalized sum of the first
`r` coordinates `(ω k - m) / σ` of the infinite product. -/
private lemma law_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] (m σ : ℝ) (r : ℕ) :
    (Measure.pi fun _ : Fin r => μ).map
        (fun y : Fin r → ℝ => ((∑ i, y i) - r * m) / (σ * Real.sqrt r)) =
      (Measure.infinitePi fun _ : ℕ => μ).map (fun ω : ℕ → ℝ =>
        (Real.sqrt (r : ℝ))⁻¹ * ∑ k ∈ Finset.range r, (ω k - m) / σ) := by
  have hf : Measurable fun y : Fin r → ℝ => ((∑ i, y i) - r * m) / (σ * Real.sqrt r) :=
    ((Finset.measurable_sum _ fun i _ => measurable_pi_apply i).sub_const _).div_const _
  have hι : Measurable fun (ω : ℕ → ℝ) (i : Fin r) => ω i :=
    measurable_pi_iff.2 fun i => measurable_eval i
  rw [← map_restrict_eq_pi μ r, Measure.map_map hf hι]
  congr 1
  funext ω
  have hsum : ∑ i : Fin r, ω i = ∑ k ∈ Finset.range r, ω k := Fin.sum_univ_eq_sum_range ω r
  simp only [Function.comp_apply]
  rw [hsum, ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  ring

/-- The coordinates `(ω k - m) / σ` of the infinite product law are independent, identically
distributed, bounded by `(K + |m|) / σ`, centred and of variance one. -/
private lemma coordinate_facts (μ : Measure ℝ) [IsProbabilityMeasure μ] (K : ℝ)
    (hK : ∀ᵐ t ∂μ, |t| ≤ K) (m σ : ℝ) (hσ : 0 < σ) (hm : ∫ t : ℝ, t ∂μ = m)
    (hvar : ∫ t : ℝ, (t - m) ^ 2 ∂μ = σ ^ 2) :
    (∀ k : ℕ, Measurable fun ω : ℕ → ℝ => (ω k - m) / σ) ∧
      iIndepFun (fun (k : ℕ) (ω : ℕ → ℝ) => (ω k - m) / σ) (Measure.infinitePi fun _ : ℕ => μ) ∧
      (∀ k : ℕ, ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => μ), |(ω k - m) / σ| ≤ (K + |m|) / σ) ∧
      (∀ k : ℕ, ∫ ω, (ω k - m) / σ ∂(Measure.infinitePi fun _ : ℕ => μ) = 0) ∧
      (∀ k : ℕ, ∫ ω, ((ω k - m) / σ) ^ 2 ∂(Measure.infinitePi fun _ : ℕ => μ) = 1) ∧
      (∀ i : ℕ, IdentDistrib (fun ω : ℕ → ℝ => (ω i - m) / σ) (fun ω : ℕ → ℝ => (ω 0 - m) / σ)
        (Measure.infinitePi fun _ : ℕ => μ) (Measure.infinitePi fun _ : ℕ => μ)) := by
  have hg : Measurable fun t : ℝ => (t - m) / σ := (measurable_id.sub_const m).div_const σ
  have hmeas : ∀ k : ℕ, Measurable fun ω : ℕ → ℝ => (ω k - m) / σ :=
    fun k => ((measurable_eval k).sub_const m).div_const σ
  -- integrals over the product law reduce to integrals over `μ`
  have hmap : ∀ (f : ℝ → ℝ), Measurable f → ∀ k : ℕ,
      ∫ ω, f (ω k) ∂(Measure.infinitePi fun _ : ℕ => μ) = ∫ t, f t ∂μ := by
    intro f hf k
    calc ∫ ω, f (ω k) ∂(Measure.infinitePi fun _ : ℕ => μ)
        = ∫ t, f t ∂((Measure.infinitePi fun _ : ℕ => μ).map fun ω => ω k) :=
          (integral_map (measurable_pi_apply k).aemeasurable hf.aestronglyMeasurable).symm
      _ = ∫ t, f t ∂μ := by rw [Measure.infinitePi_map_eval (fun _ : ℕ => μ) k]
  have hlaw : ∀ k : ℕ, (Measure.infinitePi fun _ : ℕ => μ).map
      (fun ω : ℕ → ℝ => (ω k - m) / σ) = μ.map fun t : ℝ => (t - m) / σ := by
    intro k
    rw [show (fun ω : ℕ → ℝ => (ω k - m) / σ) =
        (fun t : ℝ => (t - m) / σ) ∘ (fun ω : ℕ → ℝ => ω k) from rfl,
      ← Measure.map_map hg (measurable_pi_apply k),
      Measure.infinitePi_map_eval (fun _ : ℕ => μ) k]
  have hint : Integrable (fun t : ℝ => t) μ := integrable_of_abs_le measurable_id hK
  refine ⟨hmeas, ?_, ?_, ?_, ?_, ?_⟩
  · exact iIndepFun_infinitePi (P := fun _ : ℕ => μ) (X := fun _ t => (t - m) / σ)
      (fun _ => hg)
  · intro k
    have hk : ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => μ), |ω k| ≤ K :=
      ae_of_ae_map (f := fun x : ℕ → ℝ => x k) (p := fun t : ℝ => |t| ≤ K)
        (measurable_pi_apply k).aemeasurable
        (by rw [Measure.infinitePi_map_eval (fun _ : ℕ => μ) k]; exact hK)
    filter_upwards [hk] with ω h
    rw [abs_div, abs_of_pos hσ]
    have h' : |ω k - m| ≤ K + |m| :=
      abs_le.2 ⟨by linarith [abs_le.1 h, le_abs_self m], by linarith [abs_le.1 h, neg_le_abs m]⟩
    gcongr
  · intro k
    rw [hmap (fun t => (t - m) / σ) hg k, integral_div, integral_sub hint (integrable_const m), hm,
      integral_const]
    simp
  · intro k
    rw [hmap (fun t => ((t - m) / σ) ^ 2) (hg.pow_const 2) k]
    simp_rw [div_pow]
    rw [integral_div, hvar, div_self (pow_ne_zero 2 hσ.ne')]
  · intro i
    exact ⟨(hmeas i).aemeasurable, (hmeas 0).aemeasurable, by rw [hlaw i, hlaw 0]⟩

/-- The central limit theorem step: Mathlib's central limit theorem and the portmanteau theorem give
the convergence of the distribution function of the normalized sum at every level `x`. -/
private lemma clt_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ] (K : ℝ)
    (hK : ∀ᵐ t ∂μ, |t| ≤ K) (m σ : ℝ) (hσ : 0 < σ) (hm : ∫ t : ℝ, t ∂μ = m)
    (hvar : ∫ t : ℝ, (t - m) ^ 2 ∂μ = σ ^ 2) (x : ℝ) :
    Tendsto (fun r : ℕ => ((Measure.infinitePi fun _ : ℕ => μ).map (fun ω : ℕ → ℝ =>
        (Real.sqrt (r : ℝ))⁻¹ * ∑ k ∈ Finset.range r, (ω k - m) / σ)).real (Iic x)) atTop
      (𝓝 ((gaussianReal 0 1).real (Iic x))) := by
  obtain ⟨-, hind, -, h0, h2, hid⟩ := coordinate_facts μ K hK m σ hσ hm hvar
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum
    (P := Measure.infinitePi fun _ : ℕ => μ) (P' := gaussianReal 0 1)
    (X := fun (k : ℕ) (ω : ℕ → ℝ) => (ω k - m) / σ) (Y := id) HasLaw.id (h0 0) (h2 0) hind hid
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  have hnull : (Measure.map id (gaussianReal 0 1)) (frontier (Iic x)) = 0 := by
    rw [Measure.map_id, frontier_Iic]
    exact measure_singleton x
  have h1 := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hclt.tendsto
    (E := Iic x) hnull
  change Tendsto (fun r : ℕ => ((Measure.infinitePi fun _ : ℕ => μ).map (fun ω : ℕ → ℝ =>
      (Real.sqrt (r : ℝ))⁻¹ * ∑ k ∈ Finset.range r, (ω k - m) / σ)) (Iic x)) atTop
      (𝓝 ((Measure.map id (gaussianReal 0 1)) (Iic x))) at h1
  rw [Measure.map_id] at h1
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h1

/-- **Lemma 4.5, the square-root distance to the normal law** (Martin 2004, proof of Lemma 4.5, with
the central limit theorem in place of the cited rate). For a law `μ` with bounded support, mean `m`
and variance `σ ^ 2 > 0`, the square-root distance `∫ |F~^(r)(x) - Φ(x)|^(1/2) dx` between the
distribution function of the normalized sum `(X_1 + ... + X_r - r m) / (σ √r)` of `r` independent
copies and that of the standard normal law tends to `0` as `r` tends to infinity. The qualitative
limit replaces the rate `C r^(-1/4)` of Martin's proof. -/
theorem sqrt_cdf_distance_normalized_sum_tendsto_zero
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (K : ℝ) (hK : ∀ᵐ t ∂μ, |t| ≤ K)
    (m σ : ℝ) (hσ : 0 < σ) (hm : ∫ t : ℝ, t ∂μ = m)
    (hvar : ∫ t : ℝ, (t - m) ^ 2 ∂μ = σ ^ 2) :
    Tendsto (fun r : ℕ => sqrtCdfDistance ((Measure.pi (fun _ : Fin r => μ)).map
      (fun y : Fin r → ℝ => ((∑ i, y i) - r * m) / (σ * Real.sqrt r)))
      (gaussianReal 0 1)) atTop (𝓝 0) := by
  obtain ⟨hmeas, hind, hbd, h0, h2, -⟩ := coordinate_facts μ K hK m σ hσ hm hvar
  simp_rw [law_eq μ m σ]
  have hB4 : 0 ≤ ((K + |m|) / σ) ^ 4 := by positivity
  refine sqrt_distance_tendsto (A := ((K + |m|) / σ) ^ 4 + 11) (by positivity) ?_ ?_
    (clt_cdf μ K hK m σ hσ hm hvar)
  · intro r t ht
    obtain ⟨h1, h2'⟩ := normalized_tail (Y := fun (k : ℕ) (ω : ℕ → ℝ) => (ω k - m) / σ)
      hmeas hind hbd h0 h2 r ht
    exact ⟨h1.trans (div_pow_mono ht (by linarith)), h2'.trans (div_pow_mono ht (by linarith))⟩
  · intro t ht
    obtain ⟨h1, h2'⟩ := gaussian_tail ht
    exact ⟨h1.trans (div_pow_mono ht (by linarith)), h2'.trans (div_pow_mono ht (by linarith))⟩

/-- **Lemma 4.5, the square-root distance to the normal law, in the form used by the later steps**
(Martin 2004, proof of Lemma 4.5). Let `ν k` be the law of the sum of `k` independent copies of a
law `μ` with bounded support, mean `m` and variance `σ ^ 2 > 0`. Then the square-root distance
between the law of `(X_1 + ... + X_r - r m) / (σ √r)` (the law `F~^(r)`) and the standard normal law
tends to `0` as `r` tends to infinity. -/
theorem sqrt_cdf_distance_sum_law_tendsto_zero
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (K : ℝ) (hK : ∀ᵐ t ∂μ, |t| ≤ K)
    (m σ : ℝ) (hσ : 0 < σ) (hm : ∫ t : ℝ, t ∂μ = m)
    (hvar : ∫ t : ℝ, (t - m) ^ 2 ∂μ = σ ^ 2)
    (ν : ℕ → Measure ℝ)
    (hν : ∀ k, ν k = (Measure.pi (fun _ : Fin k => μ)).map (fun y => ∑ i, y i)) :
    Tendsto (fun r : ℕ => sqrtCdfDistance ((ν r).map
      (fun s : ℝ => (s - r * m) / (σ * Real.sqrt r))) (gaussianReal 0 1)) atTop (𝓝 0) := by
  have e : ∀ r : ℕ, (ν r).map (fun s : ℝ => (s - r * m) / (σ * Real.sqrt r)) =
      (Measure.pi fun _ : Fin r => μ).map
        (fun y : Fin r → ℝ => ((∑ i, y i) - r * m) / (σ * Real.sqrt r)) := by
    intro r
    have hg : Measurable fun s : ℝ => (s - r * m) / (σ * Real.sqrt r) :=
      (measurable_id.sub_const _).div_const _
    have hf : Measurable fun y : Fin r → ℝ => ∑ i, y i :=
      Finset.measurable_sum _ fun i _ => measurable_pi_apply i
    rw [hν r, Measure.map_map hg hf]
    rfl
  simp only [e]
  exact sqrt_cdf_distance_normalized_sum_tendsto_zero μ K hK m σ hσ hm hvar

end LPPDifferentiability
