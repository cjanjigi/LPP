/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.RealExpectedRateGeometry

import Mathlib.Tactic

/-! # Geometry of the expected passage rate in EReal

Martin (2004), Proposition 2.1 (ii)-(iv), concerns the function g on the closed quadrant
given by the normalized expected passage times E T(floor(n x)) / n. This file takes any
g : Quadrant → EReal with that limit property (clause (E)) and proves, in EReal, which also
contains the value +infinity: g(0) = 0, homogeneity (including scalar zero), symmetry and
superadditivity. The real-valued lemmas of `Probability/RealExpectedRateGeometry.lean` are
reused where they do not mention g. The lower bound g(x) ≥ (x₁ + x₂) m excludes minus
infinity, so every EReal sum below is continuous. -/

public section

open MeasureTheory Filter Set
open scoped Topology NNReal

namespace LPPDifferentiability

/-- An EReal sequence with limit `A`, plus a real sequence with real limit `s`, has limit
`A + s`. No side condition on `A` is needed, because the second term is real. -/
private theorem ereal_rate_tendsto_add_real {u : ℕ → EReal} {A : EReal} {v : ℕ → ℝ} {s : ℝ}
    (hu : Tendsto u atTop (𝓝 A)) (hv : Tendsto (fun n => (v n : EReal)) atTop (𝓝 (s : EReal))) :
    Tendsto (fun n => u n + (v n : EReal)) atTop (𝓝 (A + (s : EReal))) :=
  (EReal.continuousAt_add (p := (A, (s : EReal))) (Or.inr (EReal.coe_ne_bot s))
    (Or.inr (EReal.coe_ne_top s))).tendsto.comp (hu.prodMk_nhds hv)

/-- Corrected expected rates. If the expected rates at `x` tend to `A` in EReal, the corrected
rates (expectation minus length times the mean) tend to `A` minus the corrected length. -/
private theorem ereal_rate_tendsto_corrected (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (x : Quadrant) (A : EReal)
    (hA : Tendsto (fun n : ℕ => (((∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) ∂environmentLaw μ) / (n : ℝ) : ℝ) : EReal))
      atTop (𝓝 A)) :
    Tendsto (fun n : ℕ => ((((∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) ∂environmentLaw μ) -
        ((⌊(n : ℝ) * (x.1 : ℝ)⌋₊ + ⌊(n : ℝ) * (x.2 : ℝ)⌋₊ : ℕ) : ℝ) * (∫ t : ℝ, t ∂μ)) /
        (n : ℝ) : ℝ) : EReal))
      atTop (𝓝 (A + (((-(((x.1 : ℝ) + (x.2 : ℝ)) * (∫ t : ℝ, t ∂μ))) : ℝ) : EReal))) := by
  have hlen := ((tendsto_floor_pair_length (x.1 : ℝ) (x.2 : ℝ) x.1.property x.2.property).mul_const
    (∫ t : ℝ, t ∂μ)).neg
  refine Tendsto.congr (fun n => ?_) (ereal_rate_tendsto_add_real hA (EReal.tendsto_coe.mpr hlen))
  rw [← EReal.coe_add]
  congr 1
  ring

/-- Clause (E) forces `g x ≥ (x₁ + x₂) m`. Corrected monotonicity from the origin, together
with `T(0) = 0`, bounds each expected rate below by its length times the mean. -/
private theorem ereal_rate_lower_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ) (g : Quadrant → EReal)
    (hE : ∀ x : Quadrant, Tendsto (fun n : ℕ => (((∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) ∂environmentLaw μ) / (n : ℝ) : ℝ) : EReal))
      atTop (𝓝 (g x)))
    (x : Quadrant) :
    (((((x.1 : ℝ) + (x.2 : ℝ)) * (∫ t : ℝ, t ∂μ)) : ℝ) : EReal) ≤ g x := by
  have hlen := (tendsto_floor_pair_length (x.1 : ℝ) (x.2 : ℝ) x.1.property x.2.property).mul_const
    (∫ t : ℝ, t ∂μ)
  refine le_of_tendsto_of_tendsto' (EReal.tendsto_coe.mpr hlen) (hE x) (fun n => ?_)
  rw [EReal.coe_le_coe_iff]
  have hcorr := integral_lastPassage_corrected_monotone μ hμ (0, 0)
    (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) (by simp) (by simp)
  have hmul : ((⌊(n : ℝ) * (x.1 : ℝ)⌋₊ + ⌊(n : ℝ) * (x.2 : ℝ)⌋₊ : ℕ) : ℝ) * (∫ t : ℝ, t ∂μ) ≤
      ∫ ω : Environment, lastPassage ω 0 (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
        ∂environmentLaw μ := by
    simpa using hcorr
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right hmul (Nat.cast_nonneg n)

/-- Every value of `g` is above minus infinity. -/
private theorem ereal_rate_ne_bot (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ) (g : Quadrant → EReal)
    (hE : ∀ x : Quadrant, Tendsto (fun n : ℕ => (((∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) ∂environmentLaw μ) / (n : ℝ) : ℝ) : EReal))
      atTop (𝓝 (g x)))
    (x : Quadrant) : g x ≠ ⊥ :=
  bot_lt_iff_ne_bot.mp (lt_of_lt_of_le (EReal.bot_lt_coe _) (ereal_rate_lower_bound μ hμ g hE x))

/-- Passing a termwise inequality `u n + v n ≤ w n + r n` to EReal limits, when the limits of
`u` and `v` are not bottom and the correction `r` tends to zero. -/
private theorem ereal_rate_add_le_of_tendsto {u v w r : ℕ → ℝ} {A B C : EReal}
    (hA : A ≠ ⊥) (hB : B ≠ ⊥)
    (hu : Tendsto (fun n => (u n : EReal)) atTop (𝓝 A))
    (hv : Tendsto (fun n => (v n : EReal)) atTop (𝓝 B))
    (hw : Tendsto (fun n => (w n : EReal)) atTop (𝓝 C))
    (hr : Tendsto r atTop (𝓝 0))
    (h : ∀ n, u n + v n ≤ w n + r n) : A + B ≤ C := by
  have hsum : Tendsto (fun n => (u n : EReal) + (v n : EReal)) atTop (𝓝 (A + B)) :=
    (EReal.continuousAt_add (p := (A, B)) (Or.inr hB) (Or.inl hA)).tendsto.comp
      (hu.prodMk_nhds hv)
  have hwr : Tendsto (fun n => (w n : EReal) + (r n : EReal)) atTop
      (𝓝 (C + ((0 : ℝ) : EReal))) :=
    ereal_rate_tendsto_add_real hw (EReal.tendsto_coe.mpr hr)
  rw [EReal.coe_zero, add_zero] at hwr
  refine le_of_tendsto_of_tendsto' hsum hwr (fun n => ?_)
  show (u n : EReal) + (v n : EReal) ≤ (w n : EReal) + (r n : EReal)
  rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
  exact h n

/-- Real algebra behind superadditivity: a corrected inequality, divided by `n`, gives the
uncorrected inequality up to the correction `(La + Lb - Lc) m / n`. -/
private theorem ereal_rate_div_algebra (Ea Eb Ec La Lb Lc m n : ℝ) (hn : 0 ≤ n)
    (h : Ea - La * m + (Eb - Lb * m) ≤ Ec - Lc * m) :
    Ea / n + Eb / n ≤ Ec / n + (La + Lb - Lc) * m / n := by
  have hd := div_le_div_of_nonneg_right h hn
  have e1 : (Ea - La * m + (Eb - Lb * m)) / n = Ea / n + Eb / n - (La + Lb) * m / n := by ring
  have e2 : (Ec - Lc * m) / n = Ec / n - Lc * m / n := by ring
  have e3 : (La + Lb - Lc) * m / n = (La + Lb) * m / n - Lc * m / n := by ring
  linarith

/-- Clause (E) gives `g(0) = 0`, since every expected rate at the origin is zero (the empty
path carries no weight, `T(0) = 0`). Martin (2004), Proposition 2.1, with `T(0) = 0`. -/
theorem ereal_expected_rate_zero (μ : Measure ℝ) [IsProbabilityMeasure μ] (g : Quadrant → EReal)
    (hE : ∀ x : Quadrant, Tendsto (fun n : ℕ => (((∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) ∂environmentLaw μ) / (n : ℝ) : ℝ) : EReal))
      atTop (𝓝 (g x))) :
    g 0 = 0 := by
  have ht := hE 0
  simp only [Prod.fst_zero, Prod.snd_zero, NNReal.coe_zero, mul_zero, Nat.floor_zero,
    lastPassage_zero, integral_zero, zero_div, EReal.coe_zero] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

/-- Superadditivity in EReal, for all pairs of quadrant directions. Martin (2004),
Proposition 2.1 (iv), with the superadditive floor inequality (2.2). -/
theorem ereal_expected_rate_superadditive (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ) (g : Quadrant → EReal)
    (hE : ∀ x : Quadrant, Tendsto (fun n : ℕ => (((∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) ∂environmentLaw μ) / (n : ℝ) : ℝ) : EReal))
      atTop (𝓝 (g x))) :
    ∀ x y : Quadrant, g x + g y ≤ g (x.1 + y.1, x.2 + y.2) := by
  intro x y
  have hr : Tendsto (fun n : ℕ => (((((⌊(n : ℝ) * (x.1 : ℝ)⌋₊ + ⌊(n : ℝ) * (x.2 : ℝ)⌋₊ : ℕ) : ℝ) +
      ((⌊(n : ℝ) * (y.1 : ℝ)⌋₊ + ⌊(n : ℝ) * (y.2 : ℝ)⌋₊ : ℕ) : ℝ) -
      ((⌊(n : ℝ) * ((x + y).1 : ℝ)⌋₊ + ⌊(n : ℝ) * ((x + y).2 : ℝ)⌋₊ : ℕ) : ℝ)) *
      (∫ t : ℝ, t ∂μ)) / (n : ℝ))) atTop (𝓝 0) := by
    have h := ((((tendsto_floor_pair_length (x.1 : ℝ) (x.2 : ℝ) x.1.property x.2.property).add
      (tendsto_floor_pair_length (y.1 : ℝ) (y.2 : ℝ) y.1.property y.2.property)).sub
      (tendsto_floor_pair_length ((x + y).1 : ℝ) ((x + y).2 : ℝ) (x + y).1.property
        (x + y).2.property)).mul_const (∫ t : ℝ, t ∂μ))
    have hzero : ((((x.1 : ℝ) + (x.2 : ℝ)) + ((y.1 : ℝ) + (y.2 : ℝ))) -
        (((x + y).1 : ℝ) + ((x + y).2 : ℝ))) * (∫ t : ℝ, t ∂μ) = 0 := by
      simp only [Prod.fst_add, Prod.snd_add, NNReal.coe_add]
      ring
    rw [hzero] at h
    refine Tendsto.congr (fun n => ?_) h
    ring
  refine ereal_rate_add_le_of_tendsto (ereal_rate_ne_bot μ hμ g hE x)
    (ereal_rate_ne_bot μ hμ g hE y) (hE x) (hE y) (hE (x + y)) hr (fun n => ?_)
  have hc : (∫ ω : Environment, lastPassage ω 0 (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
        ∂environmentLaw μ) -
      ((⌊(n : ℝ) * (x.1 : ℝ)⌋₊ + ⌊(n : ℝ) * (x.2 : ℝ)⌋₊ : ℕ) : ℝ) * (∫ t : ℝ, t ∂μ) +
      ((∫ ω : Environment, lastPassage ω 0 (⌊(n : ℝ) * (y.1 : ℝ)⌋₊, ⌊(n : ℝ) * (y.2 : ℝ)⌋₊)
        ∂environmentLaw μ) -
      ((⌊(n : ℝ) * (y.1 : ℝ)⌋₊ + ⌊(n : ℝ) * (y.2 : ℝ)⌋₊ : ℕ) : ℝ) * (∫ t : ℝ, t ∂μ)) ≤
      (∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * ((x + y).1 : ℝ)⌋₊, ⌊(n : ℝ) * ((x + y).2 : ℝ)⌋₊) ∂environmentLaw μ) -
      ((⌊(n : ℝ) * ((x + y).1 : ℝ)⌋₊ + ⌊(n : ℝ) * ((x + y).2 : ℝ)⌋₊ : ℕ) : ℝ) *
        (∫ t : ℝ, t ∂μ) :=
    corrected_integral_lastPassage_floor_superadditive μ hμ x y n
  exact ereal_rate_div_algebra _ _ _ _ _ _ _ _ (Nat.cast_nonneg n) hc

/-- Symmetry in EReal: exchanging the two coordinates of a direction does not change `g`.
Martin (2004), Proposition 2.1 (iii); the expected rates agree term by term by the
swap identity for last-passage times. -/
theorem ereal_expected_rate_swap (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ) (g : Quadrant → EReal)
    (hE : ∀ x : Quadrant, Tendsto (fun n : ℕ => (((∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) ∂environmentLaw μ) / (n : ℝ) : ℝ) : EReal))
      atTop (𝓝 (g x))) :
    ∀ x : Quadrant, g (x.2, x.1) = g x := by
  intro x
  change g x.swap = g x
  have heq (n : ℕ) :
      (∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.swap.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.swap.2 : ℝ)⌋₊) ∂environmentLaw μ) =
      (∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) ∂environmentLaw μ) := by
    simpa only [Prod.swap_zero, Prod.fst_swap, Prod.snd_swap, Prod.swap_prod_mk] using
      (integrable_and_integral_lastPassage_swap μ hμ 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)).2.2
  have ht := hE x.swap
  have hs : (fun n : ℕ => (((∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.swap.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.swap.2 : ℝ)⌋₊) ∂environmentLaw μ) /
        (n : ℝ) : ℝ) : EReal)) =
      (fun n : ℕ => (((∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) ∂environmentLaw μ) / (n : ℝ) : ℝ) :
          EReal)) := by
    funext n
    rw [heq n]
  rw [hs] at ht
  exact tendsto_nhds_unique ht (hE x)

/-- Floor scaling: for a natural number `n` and a quadrant scalar `c`, the floor at `⌊n c⌋`
times `t` is at most `n c t`, coordinatewise. Used to compare adjacent integer times. -/
private theorem ereal_rate_floor_scale_le (n : ℕ) (c t : ℝ≥0) :
    ⌊((⌊(n : ℝ) * (c : ℝ)⌋₊ : ℕ) : ℝ) * (t : ℝ)⌋₊ ≤ ⌊(n : ℝ) * ((c * t : ℝ≥0) : ℝ)⌋₊ := by
  apply Nat.floor_mono
  rw [NNReal.coe_mul]
  have hlo : ((⌊(n : ℝ) * (c : ℝ)⌋₊ : ℕ) : ℝ) ≤ (n : ℝ) * (c : ℝ) :=
    Nat.floor_le (by positivity)
  calc ((⌊(n : ℝ) * (c : ℝ)⌋₊ : ℕ) : ℝ) * (t : ℝ) ≤ ((n : ℝ) * (c : ℝ)) * (t : ℝ) :=
        mul_le_mul_of_nonneg_right hlo t.2
    _ = (n : ℝ) * ((c : ℝ) * (t : ℝ)) := by ring

/-- Infinite limits along a subsequence: if `F j / j` tends to `+infinity` and `k n / n` tends to
a positive `c`, then `F (k n) / n` tends to `+infinity`. Every term is a product of a positive
real and an EReal value, so `EReal.Tendsto.mul` applies with `c * infinity = infinity`. -/
private theorem ereal_rate_top_subseq {F : ℕ → ℝ} {c : ℝ} (hc : 0 < c) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hkr : Tendsto (fun n : ℕ => (k n : ℝ) / (n : ℝ)) atTop (𝓝 c))
    (hF : Tendsto (fun j : ℕ => ((F j / (j : ℝ) : ℝ) : EReal)) atTop (𝓝 ⊤)) :
    Tendsto (fun n : ℕ => ((F (k n) / (n : ℝ) : ℝ) : EReal)) atTop (𝓝 ⊤) := by
  have hc' : ((c : ℝ) : EReal) ≠ 0 := EReal.coe_ne_zero.mpr hc.ne'
  have h := EReal.Tendsto.mul (EReal.tendsto_coe.mpr hkr) (hF.comp hk)
    (Or.inl hc') (Or.inl hc') (Or.inl (EReal.coe_ne_bot c)) (Or.inl (EReal.coe_ne_top c))
  rw [EReal.coe_mul_top_of_pos hc] at h
  refine Tendsto.congr' ?_ h
  filter_upwards [hk.eventually_gt_atTop 0, eventually_ne_atTop 0] with n hn hn0
  simp only [Function.comp_apply]
  rw [← EReal.coe_mul]
  congr 1
  have h1 : ((k n : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have h2 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  field_simp

/-- Homogeneity in EReal, for every nonnegative scalar, including zero. Martin (2004),
Proposition 2.1 (ii). Positive scalars use adjacent integer times and the corrected
monotonicity; scalar zero uses `g(0) = 0` and `0 * a = 0` in EReal. -/
theorem ereal_expected_rate_smul (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ) (g : Quadrant → EReal)
    (hE : ∀ x : Quadrant, Tendsto (fun n : ℕ => (((∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) ∂environmentLaw μ) / (n : ℝ) : ℝ) : EReal))
      atTop (𝓝 (g x))) :
    ∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = ((c : ℝ) : EReal) * g x := by
  intro c x
  change g (c • x) = ((c : ℝ) : EReal) * g x
  by_cases hc : c = 0
  · subst hc
    simp only [zero_smul, NNReal.coe_zero, EReal.coe_zero, EReal.zero_mul]
    exact ereal_expected_rate_zero μ g hE
  have hcpos : (0 : ℝ≥0) < c := pos_iff_ne_zero.mpr hc
  have hc0 : (0 : ℝ) < (c : ℝ) := NNReal.coe_pos.mpr hcpos
  have hc1 : ((c • x).1 : ℝ) = (c : ℝ) * (x.1 : ℝ) := by
    rw [Prod.smul_fst, smul_eq_mul, NNReal.coe_mul]
  have hc2 : ((c • x).2 : ℝ) = (c : ℝ) * (x.2 : ℝ) := by
    rw [Prod.smul_snd, smul_eq_mul, NNReal.coe_mul]
  have hlenc := (tendsto_floor_pair_length ((c • x).1 : ℝ) ((c • x).2 : ℝ) (c • x).1.property
    (c • x).2.property).mul_const (∫ t : ℝ, t ∂μ)
  have hB : Monotone (fun z : ℕ × ℕ => (∫ ω : Environment, lastPassage ω 0 z ∂environmentLaw μ) -
      ((z.1 + z.2 : ℕ) : ℝ) * (∫ t : ℝ, t ∂μ)) :=
    fun z w hzw => integral_lastPassage_corrected_monotone μ hμ z w hzw.1 hzw.2
  by_cases htop : g x = ⊤
  · -- Infinite case: the corrected rate at `n c x` is squeezed below by the rate at `k_n x`.
    have hA0 : Tendsto (fun n : ℕ => (((∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) ∂environmentLaw μ) / (n : ℝ) : ℝ) : EReal))
        atTop (𝓝 ⊤) := by
      rw [← htop]
      exact hE x
    have hcorr := ereal_rate_tendsto_corrected μ x ⊤ hA0
    rw [EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)] at hcorr
    have hk : Tendsto (fun n : ℕ => ⌊(n : ℝ) * (c : ℝ)⌋₊) atTop atTop := by
      simpa only [mul_comm] using tendsto_nat_floor_mul_atTop (c : ℝ) hc0
    have hkr : Tendsto (fun n : ℕ => ((⌊(n : ℝ) * (c : ℝ)⌋₊ : ℕ) : ℝ) / (n : ℝ)) atTop
        (𝓝 (c : ℝ)) :=
      tendsto_nat_floor_mul_div_nat (c : ℝ) c.property
    have hsub := ereal_rate_top_subseq (F := fun j : ℕ => (∫ ω : Environment, lastPassage ω 0
        (⌊(j : ℝ) * (x.1 : ℝ)⌋₊, ⌊(j : ℝ) * (x.2 : ℝ)⌋₊) ∂environmentLaw μ) -
        ((⌊(j : ℝ) * (x.1 : ℝ)⌋₊ + ⌊(j : ℝ) * (x.2 : ℝ)⌋₊ : ℕ) : ℝ) * (∫ t : ℝ, t ∂μ))
      hc0 hk hkr hcorr
    have hlow := ereal_rate_tendsto_add_real hsub (EReal.tendsto_coe.mpr hlenc)
    rw [EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)] at hlow
    have hTop : Tendsto (fun n : ℕ => (((∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * ((c • x).1 : ℝ)⌋₊, ⌊(n : ℝ) * ((c • x).2 : ℝ)⌋₊) ∂environmentLaw μ) /
        (n : ℝ) : ℝ) : EReal)) atTop (𝓝 ⊤) := by
      refine tendsto_nhds_top_mono hlow (Eventually.of_forall fun n => ?_)
      dsimp only
      rw [← EReal.coe_add, EReal.coe_le_coe_iff]
      have hmono := integral_lastPassage_corrected_monotone μ hμ
        (⌊((⌊(n : ℝ) * (c : ℝ)⌋₊ : ℕ) : ℝ) * (x.1 : ℝ)⌋₊,
          ⌊((⌊(n : ℝ) * (c : ℝ)⌋₊ : ℕ) : ℝ) * (x.2 : ℝ)⌋₊)
        (⌊(n : ℝ) * ((c • x).1 : ℝ)⌋₊, ⌊(n : ℝ) * ((c • x).2 : ℝ)⌋₊)
        (ereal_rate_floor_scale_le n c x.1) (ereal_rate_floor_scale_le n c x.2)
      calc _ ≤ ((∫ ω : Environment, lastPassage ω 0
              (⌊(n : ℝ) * ((c • x).1 : ℝ)⌋₊, ⌊(n : ℝ) * ((c • x).2 : ℝ)⌋₊) ∂environmentLaw μ) -
            ((⌊(n : ℝ) * ((c • x).1 : ℝ)⌋₊ + ⌊(n : ℝ) * ((c • x).2 : ℝ)⌋₊ : ℕ) : ℝ) *
              (∫ t : ℝ, t ∂μ)) / (n : ℝ) +
          ((((⌊(n : ℝ) * ((c • x).1 : ℝ)⌋₊ + ⌊(n : ℝ) * ((c • x).2 : ℝ)⌋₊ : ℕ) : ℝ) /
            (n : ℝ)) * (∫ t : ℝ, t ∂μ)) :=
            add_le_add (div_le_div_of_nonneg_right hmono (Nat.cast_nonneg n)) le_rfl
        _ = (∫ ω : Environment, lastPassage ω 0
              (⌊(n : ℝ) * ((c • x).1 : ℝ)⌋₊, ⌊(n : ℝ) * ((c • x).2 : ℝ)⌋₊) ∂environmentLaw μ) /
            (n : ℝ) := by ring
    rw [htop, EReal.coe_mul_top_of_pos hc0]
    exact tendsto_nhds_unique (hE (c • x)) hTop
  · -- Finite case: the corrected real rate is homogeneous of degree one (real lemma).
    obtain ⟨r, hgr⟩ : ∃ r : ℝ, g x = (r : EReal) :=
      ⟨(g x).toReal, (EReal.coe_toReal htop (ereal_rate_ne_bot μ hμ g hE x)).symm⟩
    have hA : Tendsto (fun n : ℕ => (((∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) ∂environmentLaw μ) / (n : ℝ) : ℝ) : EReal))
        atTop (𝓝 (r : EReal)) := by
      rw [← hgr]
      exact hE x
    have hcorr := ereal_rate_tendsto_corrected μ x (r : EReal) hA
    rw [← EReal.coe_add] at hcorr
    have hreal := EReal.tendsto_coe.mp hcorr
    have htB := tendsto_real_scaled_floor_of_monotone
      (fun z : ℕ × ℕ => (∫ ω : Environment, lastPassage ω 0 z ∂environmentLaw μ) -
        ((z.1 + z.2 : ℕ) : ℝ) * (∫ t : ℝ, t ∂μ))
      hB x (r + -(((x.1 : ℝ) + (x.2 : ℝ)) * (∫ t : ℝ, t ∂μ))) hreal c hcpos
    have hF : Tendsto (fun n : ℕ => (∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * ((c • x).1 : ℝ)⌋₊, ⌊(n : ℝ) * ((c • x).2 : ℝ)⌋₊) ∂environmentLaw μ) /
        (n : ℝ)) atTop (𝓝 ((c : ℝ) * r)) := by
      have h2 := htB.add hlenc
      have hval : (c : ℝ) * (r + -(((x.1 : ℝ) + (x.2 : ℝ)) * (∫ t : ℝ, t ∂μ))) +
          (((c • x).1 : ℝ) + ((c • x).2 : ℝ)) * (∫ t : ℝ, t ∂μ) = (c : ℝ) * r := by
        rw [hc1, hc2]
        ring
      rw [hval] at h2
      refine Tendsto.congr (fun n => ?_) h2
      dsimp only
      ring
    rw [hgr, ← EReal.coe_mul]
    exact tendsto_nhds_unique (hE (c • x)) (EReal.tendsto_coe.mpr hF)

end LPPDifferentiability
