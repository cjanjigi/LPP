/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import LPP_Foundations.Frozen.Model.LastPassage
public import LPP_Foundations.Frozen.Model.Quadrant
public import LPP_Foundations.Probability.MartinFirstMoment
public import Martin2004.Probability.ShapeComparisonBound
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecificLimits.Basic
import Martin2004.Probability.MaximumQuantileMeasurability

@[expose] public section

/-!
# Comparison of two limit shapes (Martin 2004, Lemma 4.2)

Martin (2004), Lemma 4.2. For two weight laws with finite integrated square-root tails, the shapes
at `(1, α)` differ by `(1 + α)(m1 - m2)` up to `2 √(α (1 + α)) ∫ |F1 - F2|^(1/2)`.

The finite-box inequality is in `ShapeComparisonBound.lean`. Here the box is `(n, ⌊n α⌋)`; the bound
is divided by `n` and the limit is taken with the expected-rate hypotheses at the point `(1, α)`.
The limit is therefore taken after the integral over the level, not inside it as in Martin's proof,
so the dominated convergence step, whose majorant Martin omits, is not needed.

* `shape_sub_le_cdf_integral`: one direction, for an integrable `|F1 - F2|^(1/2)`.
* `martin_lemma_4_2`: both directions, with the right side in `[0, ∞]`.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace LPPDifferentiability

/-! ### One direction: the limit of the finite-box bound -/

/-- Martin (2004), proof of Lemma 4.2, one direction. If `|F1 - F2|^(1/2)` is integrable, then
`g1(1, α) - g2(1, α) - (1 + α)(m1 - m2) ≤ 2 √(α (1 + α)) ∫ |F1 - F2|^(1/2)`. The finite-box bound
holds at every `n` for the box `(n, ⌊n α⌋)`; dividing by `n` and letting `n → ∞` gives the claim. -/
theorem shape_sub_le_cdf_integral (μ₁ μ₂ : Measure ℝ) [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] (h₁ : Integrable (fun t : ℝ => t) μ₁)
    (h₂ : Integrable (fun t : ℝ => t) μ₂)
    (hG : Integrable (fun s : ℝ => |μ₁.real (Iic s) - μ₂.real (Iic s)| ^ (1 / 2 : ℝ)))
    (g₁ g₂ : Quadrant → ℝ)
    (hg₁ : ∀ x : Quadrant, Tendsto (fun n : ℕ =>
        (∫ ω : Environment, lastPassage ω 0
          (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
          ∂environmentLaw μ₁) / (n : ℝ)) atTop (𝓝 (g₁ x)))
    (hg₂ : ∀ x : Quadrant, Tendsto (fun n : ℕ =>
        (∫ ω : Environment, lastPassage ω 0
          (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
          ∂environmentLaw μ₂) / (n : ℝ)) atTop (𝓝 (g₂ x)))
    (α : ℝ≥0) :
    g₁ (1, α) - g₂ (1, α) - (1 + (α : ℝ)) * ((∫ t : ℝ, t ∂μ₁) - ∫ t : ℝ, t ∂μ₂) ≤
      2 * Real.sqrt ((α : ℝ) * (1 + (α : ℝ))) *
        ∫ s : ℝ, |μ₁.real (Iic s) - μ₂.real (Iic s)| ^ (1 / 2 : ℝ) := by
  have ha : 0 ≤ (α : ℝ) := NNReal.coe_nonneg α
  set D : ℝ := (∫ t : ℝ, t ∂μ₁) - ∫ t : ℝ, t ∂μ₂ with hD
  set C : ℝ := ∫ s : ℝ, |μ₁.real (Iic s) - μ₂.real (Iic s)| ^ (1 / 2 : ℝ) with hC
  -- the floor rates at the point `(1, α)`: `⌊n * 1⌋ = n`
  have hlim₁ : Tendsto (fun n : ℕ =>
      (∫ ω : Environment, lastPassage ω 0 (n, ⌊(n : ℝ) * (α : ℝ)⌋₊) ∂environmentLaw μ₁) / (n : ℝ))
      atTop (𝓝 (g₁ (1, α))) := (hg₁ (1, α)).congr fun n => by simp
  have hlim₂ : Tendsto (fun n : ℕ =>
      (∫ ω : Environment, lastPassage ω 0 (n, ⌊(n : ℝ) * (α : ℝ)⌋₊) ∂environmentLaw μ₂) / (n : ℝ))
      atTop (𝓝 (g₂ (1, α))) := (hg₂ (1, α)).congr fun n => by simp
  have hlim := hlim₁.sub hlim₂
  -- the finite-box bound divided by `n`, with `k = ⌊n α⌋`
  have hrate : ∀ n : ℕ, 1 ≤ n →
      (∫ ω : Environment, lastPassage ω 0 (n, ⌊(n : ℝ) * (α : ℝ)⌋₊) ∂environmentLaw μ₁) / (n : ℝ) -
        (∫ ω : Environment, lastPassage ω 0 (n, ⌊(n : ℝ) * (α : ℝ)⌋₊) ∂environmentLaw μ₂) / (n : ℝ)
        ≤ (1 + (⌊(n : ℝ) * (α : ℝ)⌋₊ : ℝ) / n) * D +
          2 * Real.sqrt ((1 + (⌊(n : ℝ) * (α : ℝ)⌋₊ : ℝ) / n) *
            ((⌊(n : ℝ) * (α : ℝ)⌋₊ : ℝ) / n + 1 / n)) * C := by
    intro n hn
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 hn
    set k : ℕ := ⌊(n : ℝ) * (α : ℝ)⌋₊ with hk
    have hfinite := lastPassage_mean_sub_le_cdf_bound μ₁ μ₂ h₁ h₂ hG n k
    rw [← hD, ← hC] at hfinite
    -- the square root scales by `n`
    have hinside : ((n + k : ℕ) : ℝ) * ((k : ℝ) + 1) =
        (n : ℝ) ^ 2 * ((1 + (k : ℝ) / n) * ((k : ℝ) / n + 1 / n)) := by
      push_cast
      field_simp
    have hsqrt : Real.sqrt (((n + k : ℕ) : ℝ) * ((k : ℝ) + 1)) =
        (n : ℝ) * Real.sqrt ((1 + (k : ℝ) / n) * ((k : ℝ) / n + 1 / n)) := by
      rw [hinside, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hn0.le]
    have hmain : ((n + k : ℕ) : ℝ) = (1 + (k : ℝ) / n) * n := by
      push_cast
      field_simp
    rw [← sub_div, div_le_iff₀ hn0]
    calc _ ≤ _ := hfinite
      _ = _ := by rw [hsqrt, hmain]; ring
  -- the proportions `k / n → α` and `1 / n → 0`
  have hprop : Tendsto (fun n : ℕ => (⌊(n : ℝ) * (α : ℝ)⌋₊ : ℝ) / n) atTop (𝓝 (α : ℝ)) :=
    ((tendsto_nat_floor_mul_div_atTop ha).comp tendsto_natCast_atTop_atTop).congr fun n => by
      simp [mul_comm]
  have hone : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  -- the limit of the right side
  have h1 := hprop.const_add 1
  have h2 := hprop.add hone
  have hbound := (h1.mul_const D).add (((h1.mul h2).sqrt).const_mul 2 |>.mul_const C)
  have hle := le_of_tendsto_of_tendsto hlim hbound
    (eventually_atTop.2 ⟨1, fun n hn => hrate n hn⟩)
  have hsqrt : (1 + (α : ℝ)) * ((α : ℝ) + 0) = (α : ℝ) * (1 + (α : ℝ)) := by ring
  rw [hsqrt] at hle
  linarith

/-! ### Lemma 4.2 -/

/-- **Martin (2004), Lemma 4.2**. If `g₁` and `g₂` are the limit shapes of two weight laws with
finite integrated square-root tails (2.6) and (2.7), then for every `α > 0`,
`|g₁(1, α) - g₂(1, α) - (1 + α)(m₁ - m₂)| ≤ 2 √(α (1 + α)) ∫ |F₁ - F₂|^(1/2)`. The right side is in
`[0, ∞]`; if the integral is infinite the claim is trivial. -/
theorem martin_lemma_4_2
    (μ₁ μ₂ : Measure ℝ) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (hneg₁ : (∫⁻ t in Iio (0 : ℝ), (μ₁ (Iic t)) ^ (1 / 2 : ℝ)) < ∞)
    (hpos₁ : (∫⁻ t in Ioi (0 : ℝ), (μ₁ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞)
    (hneg₂ : (∫⁻ t in Iio (0 : ℝ), (μ₂ (Iic t)) ^ (1 / 2 : ℝ)) < ∞)
    (hpos₂ : (∫⁻ t in Ioi (0 : ℝ), (μ₂ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞)
    (g₁ g₂ : Quadrant → ℝ)
    (hg₁ : ∀ x : Quadrant, Tendsto (fun n : ℕ =>
        (∫ ω : Environment, lastPassage ω 0
          (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
          ∂environmentLaw μ₁) / (n : ℝ)) atTop (𝓝 (g₁ x)))
    (hg₂ : ∀ x : Quadrant, Tendsto (fun n : ℕ =>
        (∫ ω : Environment, lastPassage ω 0
          (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
          ∂environmentLaw μ₂) / (n : ℝ)) atTop (𝓝 (g₂ x)))
    (α : ℝ≥0) (hα : 0 < α) :
    ENNReal.ofReal |g₁ (1, α) - g₂ (1, α) -
        (1 + (α : ℝ)) * ((∫ t : ℝ, t ∂μ₁) - ∫ t : ℝ, t ∂μ₂)| ≤
      ENNReal.ofReal (2 * Real.sqrt ((α : ℝ) * (1 + (α : ℝ)))) *
        ∫⁻ s : ℝ, (ENNReal.ofReal |μ₁.real (Iic s) - μ₂.real (Iic s)|) ^ (1 / 2 : ℝ) := by
  have h₁ := integrable_id_of_martin_tails μ₁ hneg₁ hpos₁
  have h₂ := integrable_id_of_martin_tails μ₂ hneg₂ hpos₂
  have hc : 0 < 2 * Real.sqrt ((α : ℝ) * (1 + (α : ℝ))) :=
    mul_pos two_pos (Real.sqrt_pos.2 (mul_pos (NNReal.coe_pos.2 hα) (by positivity)))
  by_cases hJ : (∫⁻ s : ℝ, (ENNReal.ofReal |μ₁.real (Iic s) - μ₂.real (Iic s)|) ^ (1 / 2 : ℝ)) = ⊤
  · rw [hJ, ENNReal.mul_top (ENNReal.ofReal_pos.2 hc).ne']
    exact le_top
  -- the integral is finite: `|F₁ - F₂|^(1/2)` is integrable and its real integral is `J.toReal`
  have hAbs : Measurable (fun s : ℝ => |μ₁.real (Iic s) - μ₂.real (Iic s)|) :=
    continuous_abs.measurable.comp
      ((measurable_measureReal_Iic μ₁).sub (measurable_measureReal_Iic μ₂))
  have hGm : Measurable (fun s : ℝ => |μ₁.real (Iic s) - μ₂.real (Iic s)| ^ (1 / 2 : ℝ)) :=
    hAbs.pow_const _
  have hGnn : ∀ s : ℝ, 0 ≤ |μ₁.real (Iic s) - μ₂.real (Iic s)| ^ (1 / 2 : ℝ) := fun s =>
    Real.rpow_nonneg (abs_nonneg _) _
  have hJeq : (∫⁻ s : ℝ, (ENNReal.ofReal |μ₁.real (Iic s) - μ₂.real (Iic s)|) ^ (1 / 2 : ℝ)) =
      ∫⁻ s : ℝ, ENNReal.ofReal (|μ₁.real (Iic s) - μ₂.real (Iic s)| ^ (1 / 2 : ℝ)) :=
    lintegral_congr fun s => ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)
  have hG : Integrable (fun s : ℝ => |μ₁.real (Iic s) - μ₂.real (Iic s)| ^ (1 / 2 : ℝ)) :=
    ⟨hGm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall hGnn)).2 (by rw [← hJeq]; exact lt_top_iff_ne_top.2 hJ)⟩
  have hG' : Integrable (fun s : ℝ => |μ₂.real (Iic s) - μ₁.real (Iic s)| ^ (1 / 2 : ℝ)) := by
    simpa only [abs_sub_comm] using hG
  rw [hJeq, ← ofReal_integral_eq_lintegral_ofReal hG (Filter.Eventually.of_forall hGnn),
    ← ENNReal.ofReal_mul hc.le]
  -- both directions: the second is the first with the two laws exchanged
  have e₁ := shape_sub_le_cdf_integral μ₁ μ₂ h₁ h₂ hG g₁ g₂ hg₁ hg₂ α
  have e₂ := shape_sub_le_cdf_integral μ₂ μ₁ h₂ h₁ hG' g₂ g₁ hg₂ hg₁ α
  have hsw : ∫ s : ℝ, |μ₂.real (Iic s) - μ₁.real (Iic s)| ^ (1 / 2 : ℝ) =
      ∫ s : ℝ, |μ₁.real (Iic s) - μ₂.real (Iic s)| ^ (1 / 2 : ℝ) := by
    simp only [abs_sub_comm]
  rw [hsw] at e₂
  refine ENNReal.ofReal_le_ofReal (abs_le.2 ⟨?_, e₁⟩)
  linarith

end LPPDifferentiability
