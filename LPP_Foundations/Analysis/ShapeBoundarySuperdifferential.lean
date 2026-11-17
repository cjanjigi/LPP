/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Analysis.QuadrantSuperdifferential
public import Martin2004.Shape.ExpectedRateShape
import LPP_Foundations.Analysis.AbsoluteMomentShape
import LPP_Foundations.Analysis.AbsoluteMomentAxes
import ProbabilityBasics.Analysis.SqrtBoundarySupportGap

/-! Boundary superdifferentials of the native expected-rate shape. -/

public section

open MeasureTheory LPPDifferentiability Filter Asymptotics
open scoped ENNReal NNReal Topology

namespace LPPDifferentiability

/-- Under the native moment and positive-variance assumptions, the actual
expected-rate shape has no finite supergradient at either unit axis. This is
Lemma C.2 of arXiv:1810.03580v3. -/
theorem quadrantSuperdifferential_axes_eq_empty_of_absolute_moment
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    (hvariance : 0 < ∫ t : ℝ, (t - ∫ s : ℝ, s ∂μ) ^ 2 ∂μ)
    (g : Quadrant → ℝ) (hg : IsExpectedRateShape μ g) :
    quadrantSuperdifferential g (1, 0) = ∅ ∧
      quadrantSuperdifferential g (0, 1) = ∅ := by
  let mean : ℝ := ∫ t : ℝ, t ∂μ
  let variance : ℝ := ∫ t : ℝ, (t - mean) ^ 2 ∂μ
  let sigma : ℝ := Real.sqrt variance
  have hvariance_pos : 0 < variance := by
    simpa [variance, mean] using hvariance
  have hsigma_pos : 0 < sigma := by
    dsimp [sigma]
    exact Real.sqrt_pos.2 hvariance_pos

  -- The native producer supplies the full boundary expansion and the axis values.
  have hboundary_data :=
    expected_rate_shape_boundary_asymptotics_and_second_moment_of_absolute_moment
      μ g hmoment hg
  have hboundary :
      (fun a : ℝ≥0 =>
        g (1, a) - (mean + 2 * sigma * Real.sqrt (a : ℝ))) =o[𝓝[>] (0 : ℝ≥0)]
        (fun a : ℝ≥0 => Real.sqrt (a : ℝ)) := by
    simpa [mean, variance, sigma] using hboundary_data.2
  rcases expected_rate_shape_axes_and_symmetry_of_absolute_moment
      μ hmoment g hg with ⟨hsymmetric, hfirst_axis, hsecond_axis⟩
  have hmean_first : g (1, 0) = mean := by
    simpa [mean] using hfirst_axis (1 : ℝ≥0)
  have hmean_second : g (0, 1) = mean := by
    simpa [mean] using hsecond_axis (1 : ℝ≥0)

  -- Symmetry transfers the native expansion to the other unit axis.
  have hswap (a : ℝ≥0) : g (a, 1) = g (1, a) := by
    simpa using (hsymmetric (a, 1)).symm
  have hboundary_swapped :
      (fun a : ℝ≥0 =>
        g (a, 1) - (mean + 2 * sigma * Real.sqrt (a : ℝ))) =o[𝓝[>] (0 : ℝ≥0)]
        (fun a : ℝ≥0 => Real.sqrt (a : ℝ)) := by
    have hprofiles :
        (fun a : ℝ≥0 =>
          g (a, 1) - (mean + 2 * sigma * Real.sqrt (a : ℝ))) =
        (fun a : ℝ≥0 =>
          g (1, a) - (mean + 2 * sigma * Real.sqrt (a : ℝ))) := by
      funext a
      rw [hswap a]
    rw [hprofiles]
    exact hboundary

  constructor
  · -- Test the first-axis supergradient against every point `(1, a)`.
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro v hv
    change ∀ z : Quadrant,
      v.1 * ((1 : ℝ) - (z.1 : ℝ)) +
        v.2 * ((0 : ℝ) - (z.2 : ℝ)) ≤ g (1, 0) - g z at hv
    have hupper : ∀ a : ℝ≥0, g (1, a) ≤ mean + v.2 * (a : ℝ) := by
      intro a
      have hsupport := hv (1, a)
      rw [hmean_first] at hsupport
      have hsupport' : v.2 * (-(a : ℝ)) ≤ mean - g (1, a) := by
        simpa only [NNReal.coe_one, sub_self, mul_zero, zero_sub, zero_add, add_zero] using hsupport
      nlinarith [hsupport']
    have hgap :=
      ProbabilityBasics.lt_affine_intercept_of_sqrt_asymptotic
        (fun a : ℝ≥0 => g (1, a)) mean sigma mean v.2
        hsigma_pos hboundary hupper
    exact (lt_irrefl mean) hgap
  · -- Test the second-axis supergradient against every point `(a, 1)`.
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro v hv
    change ∀ z : Quadrant,
      v.1 * ((0 : ℝ) - (z.1 : ℝ)) +
        v.2 * ((1 : ℝ) - (z.2 : ℝ)) ≤ g (0, 1) - g z at hv
    have hupper : ∀ a : ℝ≥0, g (a, 1) ≤ mean + v.1 * (a : ℝ) := by
      intro a
      have hsupport := hv (a, 1)
      rw [hmean_second] at hsupport
      have hsupport' : v.1 * (-(a : ℝ)) ≤ mean - g (a, 1) := by
        simpa only [NNReal.coe_one, sub_self, mul_zero, zero_sub, zero_add, add_zero] using hsupport
      nlinarith [hsupport']
    have hgap :=
      ProbabilityBasics.lt_affine_intercept_of_sqrt_asymptotic
        (fun a : ℝ≥0 => g (a, 1)) mean sigma mean v.1
        hsigma_pos hboundary_swapped hupper
    exact (lt_irrefl mean) hgap

end LPPDifferentiability
