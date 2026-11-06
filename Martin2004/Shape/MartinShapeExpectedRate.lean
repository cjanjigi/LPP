/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Frozen.Martin.Proposition21
public import LPP_Foundations.Probability.MartinFirstMoment
public import LPP_Foundations.Probability.EnvironmentLaw
public import Martin2004.Analysis.RationalPassageNormalization

/-!
# The sample shape is the limit of the expected rates

Martin (2004), Proposition 2.1 and Section 5.3. The shape function `g` of the
passage-time theorem is a function on the closed quadrant that is continuous, homogeneous,
concave, and satisfies `T(z) - g(z) = o(|z|)` almost surely. Proposition 2.1 describes `g` as the
limit of the expected rates `E T(floor(n x)) / n`. This file proves that any `g` with the four
properties is that limit, so the expected-rate form may be used.

The proof: the closeness property and homogeneity give almost-sure convergence of
`T(floor(n x)) / n` to `g x`. Proposition 2.1 gives almost-sure convergence of the same sequence
to the extended-real limit `g_E x` of the expected rates. One environment in both full-measure
sets shows `g_E x = g x`, so the expected rates converge to the real number `g x`.
-/

public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace LPPDifferentiability.Martin

/-- If the error `|T z - g z|` is at most `ε |z|` outside a finite set of lattice points, then it
is at most `ε |z| + M` everywhere, for one constant `M`. The constant is the sum of the errors over
the finitely many exceptional points. -/
private theorem exists_abs_error_le_add (g : Quadrant → ℝ) (T : ℕ × ℕ → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (N : ℕ) (hN : ∀ z : ℕ × ℕ, N ≤ z.1 + z.2 →
      |T z - g ((z.1 : ℝ≥0), (z.2 : ℝ≥0))| ≤ ε * ((z.1 + z.2 : ℕ) : ℝ)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℕ × ℕ,
      |T z - g ((z.1 : ℝ≥0), (z.2 : ℝ≥0))| ≤ ε * ((z.1 + z.2 : ℕ) : ℝ) + M := by
  let S : Finset (ℕ × ℕ) := Finset.range N ×ˢ Finset.range N
  let M : ℝ := ∑ z ∈ S, |T z - g ((z.1 : ℝ≥0), (z.2 : ℝ≥0))|
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun z _ => abs_nonneg _
  refine ⟨M, hM0, fun z => ?_⟩
  by_cases hz : N ≤ z.1 + z.2
  · exact (hN z hz).trans (le_add_of_nonneg_right hM0)
  · have hzS : z ∈ S := by
      simp only [S, Finset.mem_product, Finset.mem_range]
      omega
    have hle : |T z - g ((z.1 : ℝ≥0), (z.2 : ℝ≥0))| ≤ M :=
      Finset.single_le_sum (f := fun z : ℕ × ℕ => |T z - g ((z.1 : ℝ≥0), (z.2 : ℝ≥0))|)
        (fun _ _ => abs_nonneg _) hzS
    have hnn : 0 ≤ ε * ((z.1 + z.2 : ℕ) : ℝ) := mul_nonneg hε (Nat.cast_nonneg _)
    linarith only [hle, hnn]

/-- Along the lattice points `z_n = floor(n x)`, an almost-sure closeness estimate
`|T z - g z| <= ε |z|` for all large `z` gives `(T z_n - g z_n) / n -> 0`. -/
private theorem tendsto_normalized_error (g : Quadrant → ℝ) (T : ℕ × ℕ → ℝ)
    (hclose : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ z : ℕ × ℕ, N ≤ z.1 + z.2 →
      |T z - g ((z.1 : ℝ≥0), (z.2 : ℝ≥0))| ≤ ε * ((z.1 + z.2 : ℕ) : ℝ))
    (x : Quadrant) :
    Tendsto (fun n : ℕ =>
      (T (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) -
        g ((⌊(n : ℝ) * (x.1 : ℝ)⌋₊ : ℝ≥0), (⌊(n : ℝ) * (x.2 : ℝ)⌋₊ : ℝ≥0))) / (n : ℝ))
      atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  have hs : 0 ≤ (x.1 : ℝ) + x.2 := add_nonneg x.1.2 x.2.2
  have hs1 : 0 < 2 * ((x.1 : ℝ) + x.2 + 1) := by linarith only [hs]
  have hε : 0 < η / (2 * ((x.1 : ℝ) + x.2 + 1)) := div_pos hη hs1
  obtain ⟨N, hN⟩ := hclose _ hε
  obtain ⟨M, -, hM⟩ := exists_abs_error_le_add g T _ hε.le N hN
  have hlen := tendsto_floor_pair_length (x.1 : ℝ) (x.2 : ℝ) x.1.2 x.2.2
  have hbound : Tendsto (fun n : ℕ =>
      η / (2 * ((x.1 : ℝ) + x.2 + 1)) *
          (((⌊(n : ℝ) * (x.1 : ℝ)⌋₊ + ⌊(n : ℝ) * (x.2 : ℝ)⌋₊ : ℕ) : ℝ) / (n : ℝ)) +
        M / (n : ℝ)) atTop
      (𝓝 (η / (2 * ((x.1 : ℝ) + x.2 + 1)) * ((x.1 : ℝ) + x.2) + 0)) :=
    (hlen.const_mul _).add (tendsto_const_div_atTop_nhds_zero_nat M)
  have hlim : η / (2 * ((x.1 : ℝ) + x.2 + 1)) * ((x.1 : ℝ) + x.2) + 0 < η := by
    rw [add_zero, div_mul_eq_mul_div, div_lt_iff₀ hs1]
    nlinarith only [mul_pos hη (show (0 : ℝ) < (x.1 : ℝ) + x.2 + 2 by linarith only [hs])]
  filter_upwards [hbound.eventually (gt_mem_nhds hlim), eventually_gt_atTop 0] with n hn hn0
  have hn' : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 hn0
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hn']
  calc _ ≤ (η / (2 * ((x.1 : ℝ) + x.2 + 1)) *
          (((⌊(n : ℝ) * (x.1 : ℝ)⌋₊ + ⌊(n : ℝ) * (x.2 : ℝ)⌋₊ : ℕ) : ℝ)) + M) / (n : ℝ) :=
        div_le_div_of_nonneg_right (hM _) hn'.le
    _ = _ := by ring
    _ < η := hn

/-- Homogeneity and continuity give `g(floor(n x)) / n -> g x`: the quotient equals `g` at the
rescaled lattice point `floor(n x) / n`, which tends to `x`. -/
private theorem tendsto_g_floor_div (g : Quadrant → ℝ) (hcont : Continuous g)
    (hhom : ∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x)
    (x : Quadrant) :
    Tendsto (fun n : ℕ =>
      g ((⌊(n : ℝ) * (x.1 : ℝ)⌋₊ : ℝ≥0), (⌊(n : ℝ) * (x.2 : ℝ)⌋₊ : ℝ≥0)) / (n : ℝ))
      atTop (𝓝 (g x)) := by
  have hcoord : ∀ u : ℝ≥0, Tendsto (fun n : ℕ =>
      ((n : ℝ≥0)⁻¹ * (⌊(n : ℝ) * (u : ℝ)⌋₊ : ℝ≥0))) atTop (𝓝 u) := by
    intro u
    refine NNReal.tendsto_coe.mp
      ((tendsto_nat_floor_mul_div_nat (u : ℝ) u.2).congr fun n => ?_)
    simp only [NNReal.coe_mul, NNReal.coe_inv, NNReal.coe_natCast]
    rw [inv_mul_eq_div]
  have hq : Tendsto (fun n : ℕ => (((n : ℝ≥0)⁻¹ * (⌊(n : ℝ) * (x.1 : ℝ)⌋₊ : ℝ≥0)),
      ((n : ℝ≥0)⁻¹ * (⌊(n : ℝ) * (x.2 : ℝ)⌋₊ : ℝ≥0)))) atTop (𝓝 x) :=
    (hcoord x.1).prodMk_nhds (hcoord x.2)
  refine ((hcont.tendsto x).comp hq).congr fun n => ?_
  simp only [Function.comp_apply]
  rw [hhom ((n : ℝ≥0)⁻¹) ((⌊(n : ℝ) * (x.1 : ℝ)⌋₊ : ℝ≥0), (⌊(n : ℝ) * (x.2 : ℝ)⌋₊ : ℝ≥0))]
  rw [NNReal.coe_inv, NNReal.coe_natCast, inv_mul_eq_div]

/-- Martin (2004), Proposition 2.1(i) with Section 5.3: under both square-root tails, any function
`g` with the four properties of the passage-time shape (continuous, homogeneous, concave, and
`T(z) - g(z) = o(|z|)` almost surely) is the limit of the expected rates. For every direction `x`
of the closed quadrant, `E T(floor(n x)) / n` tends to `g x`. The concavity clause is part of the
hypothesis exactly as in `exists_unique_shape_martin`, and the proof does not use it. -/
theorem martin_shape_tendsto_expected_rate
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : (∫⁻ t in Iio (0 : ℝ), (μ (Iic t)) ^ (1 / 2 : ℝ)) < ∞)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞)
    (g : Quadrant → ℝ)
    (hg : Continuous g ∧
      (∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x) ∧
      (∀ (x y : Quadrant) (a b : ℝ≥0), a + b = 1 →
        (a : ℝ) * g x + (b : ℝ) * g y ≤
          g (a * x.1 + b * y.1, a * x.2 + b * y.2)) ∧
      (∀ᵐ ω ∂environmentLaw μ,
        ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ z : ℕ × ℕ,
          N ≤ z.1 + z.2 →
          |lastPassage ω (0, 0) z - g ((z.1 : ℝ≥0), (z.2 : ℝ≥0))| ≤
            ε * ((z.1 + z.2 : ℕ) : ℝ))) :
    ∀ x : Quadrant, Tendsto (fun n : ℕ =>
      (∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) ∂environmentLaw μ) / (n : ℝ))
      atTop (𝓝 (g x)) := by
  obtain ⟨hcont, hhom, -, hclose⟩ := hg
  intro x
  have hμ := integrable_id_of_martin_tails μ hneg hpos
  obtain ⟨gE, ⟨hE, hAS, -⟩, -⟩ := LPPDifferentiability.martin_prop_2_1 μ hμ
  obtain ⟨ω, hω1, hω2⟩ := (hclose.and (hAS x)).exists
  have hreal : Tendsto (fun n : ℕ =>
      lastPassage ω 0 (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) / (n : ℝ))
      atTop (𝓝 (g x)) := by
    have hsum := (tendsto_normalized_error g (lastPassage ω 0) hω1 x).add
      (tendsto_g_floor_div g hcont hhom x)
    rw [zero_add] at hsum
    refine hsum.congr fun n => ?_
    ring
  have hEq : gE x = ((g x : ℝ) : EReal) :=
    tendsto_nhds_unique hω2 (EReal.tendsto_coe.2 hreal)
  have hlim := hE x
  rw [hEq] at hlim
  exact EReal.tendsto_coe.1 hlim

end LPPDifferentiability.Martin
