/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.MartinWeakContinuity
public import Martin2004.Probability.MartinWeakNaturalRate
public import Martin2004.Probability.WeakGridRayConvergence
public import LPP_Foundations.Frozen.Model.Environment
public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import LPP_Foundations.Frozen.Model.LastPassage
public import LPP_Foundations.Frozen.Model.Quadrant
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Existence and continuity of the shape function with a finite mean

The theorem here is the proof of the statement `martin_shape_continuous` in
`Frozen/Martin/ShapeContinuous.lean` (Martin (2004), Propositions 2.1 and 2.2 and Theorem 2.3 for
`d = 2`). If the weight has a finite mean and a finite positive square-root tail integral, there
is a unique real function `g` on the closed quadrant that is the limit of the expected passage
rates, is the almost-sure and `L¹` limit along natural directions, is homogeneous, symmetric and
superadditive, and is continuous up to the boundary.

## Main results

- `martin_shape_continuous`: existence, uniqueness and continuity of the shape function.

## References

- J. B. Martin, *Limiting shape for directed percolation models*, Ann. Probab. 32 (2004),
  Propositions 2.1 and 2.2 and Theorem 2.3.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace LPPDifferentiability.Full

/-- Martin (2004), Propositions 2.1 and 2.2 and Theorem 2.3, `d = 2`, in the finite setting: if
the weight has a finite mean and the positive tail integral of `√P(X > t)` is finite, there is
exactly one real function `g` on the closed quadrant such that `E T(⌊n x⌋)/n` tends to `g x` in
every real direction; along every natural direction `a` the passage time `T(n a)/n` converges to
`g a` almost surely and in `L¹`; `g` is homogeneous, symmetric and superadditive; and `g` is
continuous on the whole closed quadrant, boundary included. -/
theorem martin_shape_continuous
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞) :
    ∃! g : Quadrant → ℝ,
      (∀ x : Quadrant, Tendsto (fun n : ℕ =>
        (∫ ω : Environment, lastPassage ω 0
          (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
          ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (g x))) ∧
      (∀ a : ℕ × ℕ, ∀ᵐ ω ∂environmentLaw μ, Tendsto
        (fun n : ℕ => lastPassage ω 0 (n • a) / (n : ℝ)) atTop
        (𝓝 (g ((a.1 : ℝ≥0), (a.2 : ℝ≥0))))) ∧
      (∀ a : ℕ × ℕ, Tendsto (fun n : ℕ => ∫ ω : Environment,
        |lastPassage ω 0 (n • a) / (n : ℝ) - g ((a.1 : ℝ≥0), (a.2 : ℝ≥0))|
          ∂environmentLaw μ) atTop (𝓝 0)) ∧
      (∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x) ∧
      (∀ x : Quadrant, g (x.2, x.1) = g x) ∧
      (∀ x y : Quadrant, g x + g y ≤ g (x.1 + y.1, x.2 + y.2)) ∧
      Continuous g := by
  -- Proposition 2.1 (i), Proposition 2.2 and Theorem 2.3 of Martin (2004):
  -- the real-direction theorem gives one function g on the closed
  -- quadrant, the limit of the expected passage rates in every real direction,
  -- together with homogeneity, symmetry, superadditivity and continuity.
  -- Its uniqueness clause is not needed here; uniqueness is proved below.
  obtain ⟨g, hP, -⟩ :=
    exists_unique_continuous_lastPassage_real_expected_rate_of_integrable_and_positive_tail
      μ hμ hpos
  obtain ⟨⟨⟨hconv, -⟩, hhom, hsup, hswap, -⟩, hcont⟩ := hP
  -- Proposition 2.1 (i), almost sure part: along every natural direction
  -- the passage time over n times the direction, divided by n, converges almost
  -- surely to the same limit g. The grid-ray theorem gives one event
  -- on which all natural directions converge at once.
  have hae : ∀ᵐ ω ∂environmentLaw μ, ∀ a : ℕ × ℕ,
      Tendsto (fun n : ℕ => lastPassage ω 0 (n • a) / (n : ℝ)) atTop
        (𝓝 (g ((a.1 : ℝ≥0), (a.2 : ℝ≥0)))) :=
    ae_lastPassage_nat_ray_limit_of_real_expected_rate μ hμ hpos g hconv
  -- Two small facts: n times a natural direction is the coordinatewise product,
  -- and the floor of n times a natural number is the product.
  have hcoords (n : ℕ) (a : ℕ × ℕ) : n • a = (n * a.1, n * a.2) := by
    cases a
    rfl
  have hfloor (n k : ℕ) : ⌊(n : ℝ) * ((k : ℝ≥0) : ℝ)⌋₊ = n * k := by
    rw [NNReal.coe_natCast, ← Nat.cast_mul, Nat.floor_natCast]
  -- Proposition 2.1 (i), L1 part: along every natural direction the
  -- L1 distance to the limit tends to zero. The natural-ray theorem
  -- gives an L1 limit for its own natural rate; that rate is the same g,
  -- because both are limits of the same expected passage rates.
  have hL1 : ∀ a : ℕ × ℕ, Tendsto (fun n : ℕ => ∫ ω : Environment,
      |lastPassage ω 0 (n • a) / (n : ℝ) - g ((a.1 : ℝ≥0), (a.2 : ℝ≥0))|
        ∂environmentLaw μ) atTop (𝓝 0) := by
    intro a
    obtain ⟨ga, hmean, -, -, hL1a⟩ :=
      exists_lastPassage_ray_convergence_of_integrable_and_positive_tail μ hμ hpos a
    have hsame : ga = g ((a.1 : ℝ≥0), (a.2 : ℝ≥0)) := by
      apply tendsto_nhds_unique hmean
      convert hconv ((a.1 : ℝ≥0), (a.2 : ℝ≥0)) using 1
      funext n
      rw [hcoords n a, hfloor n a.1, hfloor n a.2]
    rw [hsame] at hL1a
    exact hL1a
  -- Uniqueness: any function with the expected-rate limits equals g, because
  -- a sequence of real numbers has at most one limit.
  refine ⟨g, ⟨hconv, fun a => hae.mono fun ω hω => hω a, hL1,
    fun c x => hhom c x, fun x => hswap x, fun x y => hsup x y, hcont⟩, ?_⟩
  intro f hf
  funext x
  exact tendsto_nhds_unique (hf.1 x) (hconv x)

end LPPDifferentiability.Full
