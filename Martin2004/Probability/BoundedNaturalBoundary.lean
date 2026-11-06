/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.MartinNaturalShape
public import Martin2004.Probability.BoundedMarginalTails
public import ProbabilityBasics.Analysis.PlanarEntropyModulus

import Martin2004.Probability.BoundedAllocationUpperTail
import Martin2004.Probability.EntropyBorelCantelli

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Bounded natural-direction boundary estimates

The bounded marginal hypotheses supply Martin's two tails. The natural-ray
limits are actual passage limits, and the signed lower estimate uses the
path-mean lower bound independently of the upper-tail argument.
-/

public section

open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

namespace LPPDifferentiability

/-- The strict error threshold gives the strict exponent gap required by
the entropy summability calculation. -/
theorem natural_boundary_entropy_lt_exponent (a b : ℕ) {L ε : ℝ}
    (hL : 0 < L) (hab : 0 < a + b)
    (hε : 8 * L * Real.sqrt (((a + b : ℕ) : ℝ) *
      ((((a + b : ℕ) : ℝ) * Real.log (a + b : ℕ)) -
        (a : ℝ) * Real.log a - (b : ℝ) * Real.log b)) < ε) :
    (((a + b : ℕ) : ℝ) * Real.log (a + b : ℕ)) -
        (a : ℝ) * Real.log a - (b : ℝ) * Real.log b <
      ε ^ 2 / (64 * (a + b : ℕ) * L ^ 2) := by
  have hS : (0 : ℝ) < (a + b : ℕ) := by exact_mod_cast hab
  have hH : 0 ≤ (((a + b : ℕ) : ℝ) * Real.log (a + b : ℕ)) -
      (a : ℝ) * Real.log a - (b : ℝ) * Real.log b := by
    simpa only [NNReal.coe_natCast, Nat.cast_add] using
      planar_entropy_nonneg (a : ℝ≥0) (b : ℝ≥0)
  have hsq := Real.sq_sqrt (mul_nonneg hS.le hH)
  have hcrit : 0 ≤ 8 * L * Real.sqrt (((a + b : ℕ) : ℝ) *
      ((((a + b : ℕ) : ℝ) * Real.log (a + b : ℕ)) -
        (a : ℝ) * Real.log a - (b : ℝ) * Real.log b)) := by positivity
  have hstrict := mul_self_lt_mul_self hcrit hε
  apply (lt_div_iff₀ (by positivity : 0 < 64 * (a + b : ℕ) * L ^ 2)).mpr
  nlinarith only [hstrict, hsq]

/-- A probability-one convergence event intersects any probability-one
eventual upper bound. Only this single direction and threshold are used. -/
theorem lastPassage_nat_ray_limit_le_of_ae_eventually
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (a : ℕ × ℕ) (g C : ℝ)
    (hlim : ∀ᵐ ω ∂environmentLaw μ, Tendsto
      (fun n : ℕ => lastPassage ω 0 (n • a) / (n : ℝ)) atTop (𝓝 g))
    (hbound : ∀ᵐ ω ∂environmentLaw μ, ∀ᶠ n : ℕ in atTop,
      lastPassage ω 0 (n • a) < (n : ℝ) * C) : g ≤ C := by
  obtain ⟨ω, hωlim, hωbound⟩ := (hlim.and hbound).exists
  apply le_of_tendsto_of_tendsto hωlim tendsto_const_nhds
  filter_upwards [hωbound, eventually_gt_atTop (0 : ℕ)] with n hn hnpos
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  exact ((div_lt_iff₀ hnreal).mpr (by simpa only [mul_comm] using hn)).le

/-- The actual expected ray limits retain the elementary bounded-law estimate.
In particular this also handles a zero support radius without division by it. -/
theorem abs_lastPassage_nat_ray_limit_le_of_ae_abs_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (a : ℕ × ℕ) (g L : ℝ)
    (hL : 0 ≤ L) (hμ : ∀ᵐ x ∂μ, |x| ≤ L)
    (hlim : Tendsto (fun n : ℕ =>
      (∫ ω : Environment, lastPassage ω 0 (n • a) ∂environmentLaw μ) / (n : ℝ))
      atTop (𝓝 g)) : |g| ≤ ((a.1 + a.2 : ℕ) : ℝ) * L := by
  apply le_of_tendsto_of_tendsto hlim.abs tendsto_const_nhds
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have h := abs_integral_lastPassage_le_of_ae_abs_le μ L hL hμ 0 (n • a)
  have hlen : (((n • a).1 + (n • a).2 : ℕ) : ℝ) =
      (n : ℝ) * ((a.1 + a.2 : ℕ) : ℝ) := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Nat.cast_add, Nat.cast_mul]
    ring
  have hnreal : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hd := div_le_div_of_nonneg_right h (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  rw [hlen, mul_assoc, mul_div_cancel_left₀ _ hnreal] at hd
  simpa only [abs_div, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)] using hd

/-- The path-mean lower bound controls the signed boundary difference below,
including negative marginal means. -/
theorem neg_mul_le_lastPassage_nat_ray_limit_sub_vertical_mean
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (a b : ℕ) (g L : ℝ)
    (hL : 0 ≤ L) (hμ : ∀ᵐ x ∂μ, |x| ≤ L)
    (hlower : ((a + b : ℕ) : ℝ) * (∫ x : ℝ, x ∂μ) ≤ g) :
    -(a : ℝ) * L ≤ g - (b : ℝ) * (∫ x : ℝ, x ∂μ) := by
  have hm := (abs_le.mp (abs_integral_id_le_of_ae_abs_le μ L hL hμ)).1
  have hmul := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg a : (0 : ℝ) ≤ a)
  push_cast at hlower
  nlinarith only [hlower, hmul]


/-- The actual almost-sure ray limit obeys the critical upper boundary bound.
The finite allocation tail and first Borel–Cantelli are produced in the proof. -/
theorem lastPassage_nat_ray_limit_le_boundary_of_bounded
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (a b : ℕ) (g L : ℝ)
    (hL : 0 < L) (hab : 0 < a + b) (hμ : ∀ᵐ x ∂μ, |x| ≤ L)
    (hlim : ∀ᵐ ω ∂environmentLaw μ, Tendsto
      (fun n : ℕ => lastPassage ω 0 (n • (a, b)) / (n : ℝ)) atTop (𝓝 g)) :
    g ≤ (b : ℝ) * (∫ x : ℝ, x ∂μ) + a * L +
      8 * L * Real.sqrt (((a + b : ℕ) : ℝ) *
        ((((a + b : ℕ) : ℝ) * Real.log (a + b : ℕ)) -
          (a : ℝ) * Real.log a - (b : ℝ) * Real.log b)) := by
  suffices g - ((b : ℝ) * (∫ x : ℝ, x ∂μ) + a * L) ≤
      8 * L * Real.sqrt (((a + b : ℕ) : ℝ) *
        ((((a + b : ℕ) : ℝ) * Real.log (a + b : ℕ)) -
          (a : ℝ) * Real.log a - (b : ℝ) * Real.log b)) by linarith only [this]
  apply le_of_forall_gt_imp_ge_of_dense
  intro ε hε
  have hεpos : 0 < ε := lt_of_le_of_lt (by positivity) hε
  have hgap := natural_boundary_entropy_lt_exponent a b hL hab hε
  let A : ℕ → Set Environment := fun n => {ω |
    (n : ℝ) * ((b : ℝ) * (∫ x : ℝ, x ∂μ) + a * L + ε) ≤
      lastPassage ω 0 (n * a, n * b)}
  have htail : ∀ n : ℕ, 0 < n → (environmentLaw μ).real (A n) ≤
      (Nat.choose (n * (a + b)) (n * a) : ℝ) *
        Real.exp (64 - (n : ℝ) * (ε ^ 2 / (64 * (a + b : ℕ) * L ^ 2))) := by
    intro n hn
    simpa only [A, mul_div_assoc] using
      measure_lastPassage_nat_ray_ge_le_martin μ a b n hL hεpos hab hn hμ
  have hBC := ae_eventually_notMem_of_entropy_tail (environmentLaw μ) a b hgap A htail
  have hbound : ∀ᵐ ω ∂environmentLaw μ, ∀ᶠ n : ℕ in atTop,
      lastPassage ω 0 (n • (a, b)) <
        (n : ℝ) * ((b : ℝ) * (∫ x : ℝ, x ∂μ) + a * L + ε) := by
    filter_upwards [hBC] with ω hω
    filter_upwards [hω] with n hn
    have hn' : lastPassage ω 0 (n * a, n * b) <
        (n : ℝ) * ((b : ℝ) * (∫ x : ℝ, x ∂μ) + a * L + ε) :=
      lt_of_not_ge hn
    have hd : n • (a, b) = (n * a, n * b) := by ext <;> simp
    rw [hd]
    exact hn'
  have hle := lastPassage_nat_ray_limit_le_of_ae_eventually μ (a, b) g
    ((b : ℝ) * (∫ x : ℝ, x ∂μ) + a * L + ε) hlim hbound
  linarith only [hle]

/-- The same actual expected and almost-sure natural-ray limits obey the
two-sided signed boundary estimate under bounded marginal hypotheses. -/
theorem abs_lastPassage_nat_shape_sub_vertical_mean_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (L : ℝ) (hL : 0 ≤ L)
    (hμ : ∀ᵐ x ∂μ, |x| ≤ L) (g : (ℕ × ℕ) → ℝ)
    (hmean : ∀ a : ℕ × ℕ, Tendsto (fun n : ℕ =>
      (∫ ω : Environment, lastPassage ω 0 (n • a) ∂environmentLaw μ) / (n : ℝ))
      atTop (𝓝 (g a)))
    (hae : ∀ a : ℕ × ℕ, ∀ᵐ ω ∂environmentLaw μ, Tendsto
      (fun n : ℕ => lastPassage ω 0 (n • a) / (n : ℝ)) atTop (𝓝 (g a)))
    (a b : ℕ) :
    |g (a, b) - (b : ℝ) * (∫ x : ℝ, x ∂μ)| ≤
      (a : ℝ) * L + 8 * L * Real.sqrt (((a + b : ℕ) : ℝ) *
        ((((a + b : ℕ) : ℝ) * Real.log (a + b : ℕ)) -
          (a : ℝ) * Real.log a - (b : ℝ) * Real.log b)) := by
  have hi := integrable_id_of_ae_abs_le μ L hμ
  have hm := abs_integral_id_le_of_ae_abs_le μ L hL hμ
  by_cases hL0 : L = 0
  · subst L
    have hg := abs_lastPassage_nat_ray_limit_le_of_ae_abs_le μ (a, b) (g (a, b)) 0
      le_rfl hμ (hmean (a, b))
    have hg0 : g (a, b) = 0 := abs_eq_zero.mp (le_antisymm (by simpa only [mul_zero] using hg) (abs_nonneg _))
    have hm0 : (∫ x : ℝ, x ∂μ) = 0 := abs_eq_zero.mp (le_antisymm hm (abs_nonneg _))
    simp only [hg0, hm0, mul_zero, sub_zero, abs_zero, zero_mul, add_zero, le_refl]
  by_cases ha : a = 0
  · subst a
    rw [martin_ray_limit_vertical μ hi g hmean]
    simp only [sub_self, abs_zero, Nat.cast_zero, zero_mul, zero_add, sub_zero,
      sub_self, mul_zero, Real.sqrt_zero, add_zero, le_refl]
  by_cases hb : b = 0
  · subst b
    rw [martin_ray_limit_horizontal μ hi g hmean]
    simpa only [Nat.add_zero, Nat.cast_zero, zero_mul, sub_zero, sub_self,
      mul_zero, Real.sqrt_zero, add_zero, abs_mul,
      abs_of_nonneg (Nat.cast_nonneg a : (0 : ℝ) ≤ a)] using
        mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg a : (0 : ℝ) ≤ a)
  have hupper := lastPassage_nat_ray_limit_le_boundary_of_bounded μ a b (g (a, b)) L
    (lt_of_le_of_ne hL (Ne.symm hL0)) (by omega) hμ (hae (a, b))
  have hsuper := martin_ray_limit_superadditive μ hi g hmean (a, 0) (0, b)
  rw [martin_ray_limit_horizontal μ hi g hmean,
    martin_ray_limit_vertical μ hi g hmean] at hsuper
  have hlower : ((a + b : ℕ) : ℝ) * (∫ x : ℝ, x ∂μ) ≤ g (a, b) := by
    simpa [Nat.cast_add, add_mul] using hsuper
  have hl := neg_mul_le_lastPassage_nat_ray_limit_sub_vertical_mean μ a b (g (a, b))
    L hL hμ hlower
  apply abs_le.mpr
  constructor
  · have hr : 0 ≤ 8 * L * Real.sqrt (((a + b : ℕ) : ℝ) *
        ((((a + b : ℕ) : ℝ) * Real.log (a + b : ℕ)) -
          (a : ℝ) * Real.log a - (b : ℝ) * Real.log b)) := by positivity
    linarith only [hl, hr]
  · linarith only [hupper]

/-- A bounded marginal law determines one unique actual natural-direction
shape, retaining all natural convergence and geometry conclusions and the
literal entropy boundary estimate for that same function. -/
theorem exists_unique_lastPassage_natural_shape_of_ae_abs_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (L : ℝ) (hL : 0 ≤ L)
    (hμ : ∀ᵐ x ∂μ, |x| ≤ L) :
    ∃! g : (ℕ × ℕ) → ℝ,
      ((∀ a : ℕ × ℕ,
        Tendsto (fun n : ℕ =>
          (∫ ω : Environment, lastPassage ω 0 (n • a) ∂environmentLaw μ) / (n : ℝ))
          atTop (𝓝 (g a)) ∧
        g a = sSup (range (fun n : ℕ =>
          (∫ ω : Environment, lastPassage ω 0 ((n + 1) • a) ∂environmentLaw μ) /
            ((n + 1 : ℕ) : ℝ))) ∧
        (∀ᵐ ω ∂environmentLaw μ, Tendsto
          (fun n : ℕ => lastPassage ω 0 (n • a) / (n : ℝ)) atTop (𝓝 (g a))) ∧
        Tendsto (fun n : ℕ => ∫ ω : Environment,
          |lastPassage ω 0 (n • a) / (n : ℝ) - g a| ∂environmentLaw μ)
          atTop (𝓝 0)) ∧
      g 0 = 0 ∧
      (∀ (a : ℕ × ℕ) (k : ℕ), g (k • a) = (k : ℝ) * g a) ∧
      (∀ a b : ℕ × ℕ, g a + g b ≤ g (a + b)) ∧
      (∀ k : ℕ, g (k, 0) = (k : ℝ) * ∫ x : ℝ, x ∂μ) ∧
      (∀ k : ℕ, g (0, k) = (k : ℝ) * ∫ x : ℝ, x ∂μ) ∧
      (∀ a : ℕ × ℕ,
        ((a.1 + a.2 : ℕ) : ℝ) * (∫ x : ℝ, x ∂μ) ≤ g a ∧
        g a ≤ ((a.1 + a.2 : ℕ) : ℝ) * (g (1, 1) - ∫ x : ℝ, x ∂μ)) ∧
      (∀ᵐ ω ∂environmentLaw μ, ∀ a : ℕ × ℕ, Tendsto
        (fun n : ℕ => lastPassage ω 0 (n • a) / (n : ℝ)) atTop (𝓝 (g a)))) ∧
      (∀ a b : ℕ,
        |g (a, b) - (b : ℝ) * (∫ x : ℝ, x ∂μ)| ≤
          (a : ℝ) * L + 8 * L * Real.sqrt (((a + b : ℕ) : ℝ) *
            ((((a + b : ℕ) : ℝ) * Real.log (a + b : ℕ)) -
              (a : ℝ) * Real.log a - (b : ℝ) * Real.log b))) := by
  have hneg := lt_of_le_of_lt
    (integrated_negative_sqrt_tail_le_of_ae_abs_le μ L hL hμ)
    (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top : ENNReal.ofReal L < ∞)
  have hpos := lt_of_le_of_lt
    (integrated_positive_sqrt_tail_le_of_ae_abs_le μ L hL hμ)
    (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top : ENNReal.ofReal L < ∞)
  obtain ⟨g, hg, huniq⟩ := exists_unique_lastPassage_natural_shape_of_martin_tails μ hneg hpos
  refine ⟨g, ⟨hg, ?_⟩, ?_⟩
  · exact abs_lastPassage_nat_shape_sub_vertical_mean_le μ L hL hμ g
      (fun a => (hg.1 a).1) (fun a => (hg.1 a).2.2.1)
  · intro f hf
    exact huniq f hf.1

end LPPDifferentiability
