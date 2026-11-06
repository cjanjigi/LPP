/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.MartinWeakNaturalRate
public import Martin2004.Probability.MartinWeakRealExpectedRate

/-!
# Weak natural-ray convergence and finite-grid estimates

The floor-expectation limits determine the same natural rates as the almost-sure
ray theorem. On its common event, finite rectangles of natural directions
therefore have one eventual error bound.
-/

public section

open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

namespace LPPDifferentiability

/-- The floor-expectation limits identify the natural rates, so one
probability-one event gives the same almost-sure limit along every natural ray. -/
theorem ae_lastPassage_nat_ray_limit_of_real_expected_rate
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞)
    (g : Quadrant → ℝ)
    (hg : ∀ x : Quadrant, Tendsto (fun n : ℕ =>
      (∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
        ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (g x))) :
    ∀ᵐ ω ∂environmentLaw μ, ∀ a : ℕ × ℕ,
      Tendsto (fun n : ℕ => lastPassage ω 0 (n • a) / (n : ℝ)) atTop
        (𝓝 (g ((a.1 : ℝ≥0), (a.2 : ℝ≥0)))) := by
  obtain ⟨gNat, hNat, _hUnique⟩ :=
    exists_unique_lastPassage_natural_shape_of_integrable_and_positive_tail
      μ hμ hpos
  have hExpected (a : ℕ × ℕ) :
      Tendsto (fun n : ℕ =>
        (∫ ω : Environment, lastPassage ω 0 (n • a)
          ∂environmentLaw μ) / (n : ℝ)) atTop
        (𝓝 (gNat a)) := (hNat.1 a).1
  have hfloor (n k : ℕ) :
      ⌊(n : ℝ) * ((k : ℝ≥0) : ℝ)⌋₊ = n * k := by
    rw [NNReal.coe_natCast, ← Nat.cast_mul, Nat.floor_natCast]
  have hcoords (n : ℕ) (a : ℕ × ℕ) :
      n • a = (n * a.1, n * a.2) := by
    cases a
    rfl
  have hSame (a : ℕ × ℕ) :
      gNat a = g ((a.1 : ℝ≥0), (a.2 : ℝ≥0)) := by
    apply tendsto_nhds_unique (hExpected a)
    convert hg ((a.1 : ℝ≥0), (a.2 : ℝ≥0)) using 1
    funext n
    rw [hcoords n a, hfloor n a.1, hfloor n a.2]
  have hAllNat : ∀ᵐ ω ∂environmentLaw μ, ∀ a : ℕ × ℕ,
      Tendsto (fun n : ℕ => lastPassage ω 0 (n • a) / (n : ℝ)) atTop
        (𝓝 (gNat a)) := hNat.2.2.2.2.2.2.2.1
  filter_upwards [hAllNat] with ω hω
  intro a
  rw [← hSame a]
  exact hω a

/-- On one event before all natural directions, each finite square of rays
has a common threshold for the unnormalized passage-value error. -/
theorem ae_exists_common_weak_grid_ray_threshold
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞)
    (g : Quadrant → ℝ)
    (hg : ∀ x : Quadrant, Tendsto (fun n : ℕ =>
      (∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
        ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (g x))) :
    ∀ᵐ ω ∂environmentLaw μ, ∀ q : ℕ, ∀ b : ℝ, 0 < b →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ i j : ℕ,
        i ≤ 2 * q → j ≤ 2 * q →
          |lastPassage ω 0 (n • (i, j)) -
            (n : ℝ) * g ((i : ℝ≥0), (j : ℝ≥0))| ≤ b * (n : ℝ) := by
  have hAll := ae_lastPassage_nat_ray_limit_of_real_expected_rate μ hμ hpos g hg
  filter_upwards [hAll] with ω hω
  intro q b hb
  let directions : Finset (ℕ × ℕ) :=
    Finset.product (Finset.range (2 * q + 1)) (Finset.range (2 * q + 1))
  have hfinite : ∀ᶠ n : ℕ in atTop, ∀ a ∈ directions,
      dist (lastPassage ω 0 (n • a) / (n : ℝ))
        (g ((a.1 : ℝ≥0), (a.2 : ℝ≥0))) < b := by
    rw [Filter.eventually_all_finset]
    intro a ha
    exact (Metric.tendsto_nhds.mp (hω a)) b hb
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hfinite
  let N := max N₀ 1
  refine ⟨N, le_max_right N₀ 1, ?_⟩
  intro n hn i j hi hj
  have hn₀ : N₀ ≤ n := le_trans (le_max_left N₀ 1) hn
  have hmem : (i, j) ∈ directions := by
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩
  have hsmall := hN₀ n hn₀ (i, j) hmem
  have hnpos : 0 < n := by dsimp [N] at hn; omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hsmallAbs :
      |lastPassage ω 0 (n • (i, j)) / (n : ℝ) -
        g ((i : ℝ≥0), (j : ℝ≥0))| < b := by
    simpa only [Real.dist_eq] using hsmall
  have hdiv : lastPassage ω 0 (n • (i, j)) / (n : ℝ) -
      g ((i : ℝ≥0), (j : ℝ≥0)) =
        (lastPassage ω 0 (n • (i, j)) - (n : ℝ) *
          g ((i : ℝ≥0), (j : ℝ≥0))) / (n : ℝ) := by
    field_simp
  rw [hdiv, abs_div, abs_of_pos hnR] at hsmallAbs
  have herror :
      |lastPassage ω 0 (n • (i, j)) - (n : ℝ) *
        g ((i : ℝ≥0), (j : ℝ≥0))| < b * (n : ℝ) :=
    (div_lt_iff₀ hnR).mp hsmallAbs
  exact herror.le

end LPPDifferentiability
