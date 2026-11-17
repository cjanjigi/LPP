/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Shape.ExpectedRateShape
public import LPP_Foundations.Probability.MartinFirstMoment
public import Martin2004.Probability.BoundedExpectedUniform
public import Martin2004.Probability.UniformTruncationApproximation
public import Martin2004.Probability.BoundedPassageFluctuations

-- The body of `IsExpectedRateShape` is not exposed by its module; this private
-- import only lets the proof unfold the predicate.
import all Martin2004.Shape.ExpectedRateShape

/-!
# Almost-sure uniform approximation by an expected-rate shape

Martin (2004), Section 5.3 (Lemmas 5.2-5.5) together with Theorem 2.3 and
Proposition 2.1(ii). If `g` is the expected-rate shape of a law with both
integrated square-root tails finite, then `g` is continuous and homogeneous,
and almost surely the last-passage time `T(0, z)` is within `ε (z₁ + z₂)` of
`g z` for all large `z`.

The proof takes the actual expected rate `g₀` of the existence theorem,
notes that `g = g₀` because limits are unique, and then combines four errors
(clipping, centered fluctuation, clipped mean, clipped rate) at one deterministic
cutoff for each tolerance `1 / (j + 1)`. The helper lemmas are public so that `Shape/Martin.lean`,
which proves the same estimate for its own shape theorem, can use them instead of repeating them.
This file does not import `Shape/Martin.lean`.
-/

public section

open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

namespace LPPDifferentiability

/-- A homogeneity statement written with the scalar action, in coordinate form. -/
theorem coordinate_homogeneity (g : Quadrant → ℝ)
    (hg : ∀ (c : ℝ≥0) (x : Quadrant), g (c • x) = (c : ℝ) * g x)
    (c : ℝ≥0) (x : Quadrant) :
    g (c * x.1, c * x.2) = (c : ℝ) * g x := by
  exact hg c x

/-- The two clipped expected rates, both limits of the same sequence, agree. -/
theorem clipped_rates_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] (L : ℝ)
    (r b : Quadrant → ℝ)
    (hr : ∀ x : Quadrant, Tendsto (fun n : ℕ =>
      (∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
        ∂environmentLaw (μ.map (fun t : ℝ => max (-L) (min L t)))) / (n : ℝ))
      atTop (𝓝 (r x)))
    (hb : ∀ x : Quadrant, Tendsto (fun n : ℕ =>
      (∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
        ∂environmentLaw (μ.map (fun t : ℝ => max (-L) (min L t)))) / (n : ℝ))
      atTop (𝓝 (b x))) : r = b := by
  funext x
  exact tendsto_nhds_unique (hr x) (hb x)

/-- Martin Lemmas 5.2, 5.4 and 5.5 with one common cutoff `L`: the clipped rate
`r` is within `δ |x|` of `g`, the mean of the clipped passage time is within
`δ |z|` of `r z` for large `z`, and almost surely the clipped passage time is
within `δ |z|` of the true one for large `z`. -/
theorem exists_common_clipping_approximation
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : (∫⁻ t in Iio (0 : ℝ), (μ (Iic t)) ^ (1 / 2 : ℝ)) < ∞)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞)
    (g : Quadrant → ℝ)
    (hg : IsExpectedRateShape μ g)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ L : ℝ, 0 < L ∧ ∃ r : Quadrant → ℝ,
      (∀ x : Quadrant, |g x - r x| ≤ δ * ((x.1 : ℝ) + x.2)) ∧
      (∃ N : ℕ, 0 < N ∧ ∀ z : ℕ × ℕ, N ≤ z.1 + z.2 →
        |(∫ ω : Environment,
          lastPassage (fun v => max (-L) (min L (ω v))) 0 z ∂environmentLaw μ) -
          r ((z.1 : ℝ≥0), (z.2 : ℝ≥0))| < δ * ((z.1 + z.2 : ℕ) : ℝ)) ∧
      (∀ᵐ ω ∂environmentLaw μ, ∃ N : ℕ, 1 ≤ N ∧ ∀ z : ℕ × ℕ,
        N ≤ z.1 + z.2 →
        |lastPassage ω 0 z -
          lastPassage (fun v => max (-L) (min L (ω v))) 0 z| <
          δ * ((z.1 + z.2 : ℕ) : ℝ)) := by
  have hμ := integrable_id_of_martin_tails μ hneg hpos
  obtain ⟨A, _hA, htrunc⟩ := uniform_lastPassage_clipped_approximation μ hpos hneg δ hδ
  obtain ⟨B, _hB, hrate⟩ :=
    exists_clipped_real_expected_rate_relative_approximation μ hμ hpos g hg δ hδ
  let L : ℝ := max 1 (max A B)
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hAL : A ≤ L := (le_max_left A B).trans (le_max_right _ _)
  have hBL : B ≤ L := (le_max_right A B).trans (le_max_right _ _)
  obtain ⟨r, _hrc, hrm, _hro, hr⟩ := hrate L hBL
  obtain ⟨b, hb, _hub⟩ :=
    exists_unique_uniform_lastPassage_real_expected_rate_of_ae_abs_le
      (μ.map (fun t : ℝ => max (-L) (min L t))) L hL.le
      (ae_abs_le_map_clipping μ L hL.le)
  have hrb : r = b := clipped_rates_eq μ L r b hrm hb.1.1.1.1
  obtain ⟨N, hN, hmean⟩ := hb.2.2 δ hδ
  refine ⟨L, hL, r, hr, ⟨N, hN, ?_⟩, htrunc L hAL⟩
  intro z hz
  rw [hrb]
  simpa only [integral_lastPassage_map_clipping] using hmean z hz

/-- Triangle inequality for four consecutive errors, each at most `δ n`. -/
theorem four_errors_le (a b c d e δ ε n : ℝ) (hn : 0 ≤ n)
    (hδ : 4 * δ ≤ ε)
    (h₁ : |a - b| ≤ δ * n) (h₂ : |b - c| ≤ δ * n)
    (h₃ : |c - d| ≤ δ * n) (h₄ : |d - e| ≤ δ * n) :
    |a - e| ≤ ε * n := by
  calc
    |a - e| ≤ |a - b| + |b - c| + |c - d| + |d - e| := by
      calc
        |a - e| ≤ |a - d| + |d - e| := abs_sub_le a d e
        _ ≤ (|a - c| + |c - d|) + |d - e| :=
          by linarith only [abs_sub_le a c d]
        _ ≤ ((|a - b| + |b - c|) + |c - d|) + |d - e| :=
          by linarith only [abs_sub_le a b c]
    _ ≤ 4 * δ * n := by linarith only [h₁, h₂, h₃, h₄]
    _ ≤ ε * n := mul_le_mul_of_nonneg_right hδ hn

/-- A bound for every reciprocal tolerance `1 / (j + 1)` gives the bound for
every positive tolerance, almost surely (countable intersection of full
events, then a reciprocal below `ε`). -/
theorem ae_all_tolerances_of_reciprocals
    (P : Measure Environment) (F : Environment → (ℕ × ℕ) → ℝ)
    (hF : ∀ j : ℕ, ∀ᵐ ω ∂P, ∃ N : ℕ, ∀ z : ℕ × ℕ,
      N ≤ z.1 + z.2 → F ω z ≤ (1 / ((j : ℝ) + 1)) * ((z.1 + z.2 : ℕ) : ℝ)) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ z : ℕ × ℕ,
      N ≤ z.1 + z.2 → F ω z ≤ ε * ((z.1 + z.2 : ℕ) : ℝ) := by
  filter_upwards [ae_all_iff.2 hF] with ω hω
  intro ε hε
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε
  obtain ⟨N, hN⟩ := hω j
  refine ⟨N, fun z hz => (hN z hz).trans ?_⟩
  exact mul_le_mul_of_nonneg_right hj.le (Nat.cast_nonneg _)

/-- Martin (2004), Theorem 2.3, Proposition 2.1(ii) and Section 5.3. For a law with both
integrated square-root tails finite, any expected-rate shape `g` is continuous and homogeneous, and
almost surely `|T(0, z) - g z| ≤ ε (z₁ + z₂)` for all large `z`, for every
`ε > 0`. -/
theorem ae_uniform_of_isExpectedRateShape (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : (∫⁻ t in Iio (0 : ℝ), (μ (Iic t)) ^ (1 / 2 : ℝ)) < ∞)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞)
    {g : Quadrant → ℝ} (hg : IsExpectedRateShape μ g) :
    Continuous g ∧
    (∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x) ∧
    (∀ᵐ ω ∂environmentLaw μ,
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ z : ℕ × ℕ,
        N ≤ z.1 + z.2 →
        |lastPassage ω (0, 0) z - g ((z.1 : ℝ≥0), (z.2 : ℝ≥0))| ≤
          ε * ((z.1 + z.2 : ℕ) : ℝ)) := by
  have hμ := integrable_id_of_martin_tails μ hneg hpos
  obtain ⟨g₀, hg₀, _hUniqueRate⟩ :=
    exists_unique_continuous_lastPassage_real_expected_rate_of_integrable_and_positive_tail
      μ hμ hpos
  have hrate₀ : IsExpectedRateShape μ g₀ := hg₀.1.1.1
  have hgg : g = g₀ := isExpectedRateShape_unique μ hg hrate₀
  subst hgg
  have hhom := coordinate_homogeneity g hg₀.1.2.1
  have hae : ∀ᵐ ω ∂environmentLaw μ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ z : ℕ × ℕ, N ≤ z.1 + z.2 →
        |lastPassage ω (0, 0) z - g ((z.1 : ℝ≥0), (z.2 : ℝ≥0))| ≤
          ε * ((z.1 + z.2 : ℕ) : ℝ) := by
    apply ae_all_tolerances_of_reciprocals (environmentLaw μ)
      (fun ω z => |lastPassage ω (0, 0) z - g ((z.1 : ℝ≥0), (z.2 : ℝ≥0))|)
    intro j
    let τ : ℝ := 1 / ((j : ℝ) + 1)
    let δ : ℝ := τ / 8
    have hτ : 0 < τ := by dsimp only [τ]; positivity
    have hδ : 0 < δ := div_pos hτ (by norm_num)
    obtain ⟨L, hL, r, hr, ⟨Nm, _hNm, hm⟩, ht⟩ :=
      exists_common_clipping_approximation μ hneg hpos g hg₀.1.1.1 δ hδ
    have hc := ae_eventually_clipped_lastPassage_centered_uniform_deviation μ L hL
    filter_upwards [ht, hc] with ω hωt hωc
    obtain ⟨Nt, _hNt, htrunc⟩ := hωt
    obtain ⟨Nc, _hNc, hfluct⟩ := hωc δ hδ
    refine ⟨max 1 (max Nm (max Nt Nc)), ?_⟩
    intro z hz
    have hzm : Nm ≤ z.1 + z.2 :=
      (le_max_left Nm (max Nt Nc)).trans ((le_max_right 1 _).trans hz)
    have hzt : Nt ≤ z.1 + z.2 :=
      (le_max_left Nt Nc).trans ((le_max_right Nm _).trans ((le_max_right 1 _).trans hz))
    have hzc : Nc ≤ z.1 + z.2 :=
      (le_max_right Nt Nc).trans ((le_max_right Nm _).trans ((le_max_right 1 _).trans hz))
    have herr₄ := hr ((z.1 : ℝ≥0), (z.2 : ℝ≥0))
    simp only [NNReal.coe_natCast, ← Nat.cast_add] at herr₄
    rw [abs_sub_comm] at herr₄
    have hδτ : 4 * δ ≤ τ := by dsimp only [δ]; linarith only [hτ]
    exact four_errors_le _ _ _ _ _ δ τ _ (Nat.cast_nonneg _) hδτ
      (htrunc z hzt).le (hfluct z hzc).le (hm z hzm).le herr₄
  exact ⟨hg₀.2, hhom, hae⟩

end LPPDifferentiability
