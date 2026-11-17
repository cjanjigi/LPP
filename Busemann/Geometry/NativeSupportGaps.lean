/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.Definitions.SupportTilt
public import Martin2004.Shape.ExpectedRateShape
import LPP_Foundations.Analysis.AbsoluteMomentShape
import LPP_Foundations.Analysis.AbsoluteMomentAxes
import ProbabilityBasics.Probability.NonconstantVariance
import ProbabilityBasics.Analysis.SqrtBoundarySupportGap
import Busemann.Geometry.SupportIdentities

/-!
# Native strict axis gaps for every support tilt

The native boundary expansion and nonconstancy force strict separation from
both axes for any actual support tilt of the canonical expected-rate shape.
-/

public section

open LPPDifferentiability MeasureTheory Asymptotics
open scoped NNReal ENNReal Topology

namespace LPP.Busemann

/-- Under the native nonconstant absolute-moment law, every support tilt has
strict gaps at both unit axes. This supplies boundary interiority internally
for GRS1510.00860v2 (2.6)-(2.8), using JR1810.03580v3 assumption (2.1). -/
theorem support_tilt_strict_axis_gaps_of_absolute_moment
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ x, ENNReal.ofReal (|x| ^ p) ∂μ) < ∞)
    (hnonconstant : ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, x = c)
    (g : Quadrant → ℝ) (hg : IsExpectedRateShape μ g) (h : SupportTilt g) :
    g (1, 0) < -h.1.1 ∧ g (0, 1) < -h.1.2 := by
  have hgeometry := expected_rate_shape_geometry_of_absolute_moment μ g hmoment hg
  have hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z := by
    intro c z
    change g (c * z.1, c * z.2) = (c : ℝ) * g z
    exact hgeometry.2.1 c z
  -- Native moments produce the boundary expansion and positive standard deviation.
  have hboundary :=
    expected_rate_shape_boundary_asymptotics_and_second_moment_of_absolute_moment
      μ g hmoment hg
  let m : ℝ := ∫ t : ℝ, t ∂μ
  let sigma : ℝ := Real.sqrt (∫ t : ℝ, (t - ∫ s : ℝ, s ∂μ) ^ 2 ∂μ)
  have hvariance := ProbabilityBasics.integral_centered_sq_pos_of_not_ae_const
    μ hboundary.1 hnonconstant
  have hsigma : 0 < sigma := Real.sqrt_pos.mpr hvariance
  obtain ⟨ξ, hξ⟩ := h.2
  have hmajorant :=
    ((supportsAt_iff_through_origin_majorant_and_contact g ξ h.1 hhom).mp hξ).1
  have haxes := expected_rate_shape_axes_and_symmetry_of_absolute_moment μ hmoment g hg
  -- Restrict the actual global majorant to each boundary profile.
  have hfirstBound : ∀ a : ℝ≥0, g (1, a) ≤ (-h.1.1) + (-h.1.2) * (a : ℝ) := by
    intro a
    simpa only [NNReal.coe_one, mul_one] using hmajorant (1, a)
  have hsecondBound : ∀ a : ℝ≥0, g (a, 1) ≤ (-h.1.2) + (-h.1.1) * (a : ℝ) := by
    intro a
    calc
      g (a, 1) ≤ (-h.1.1) * (a : ℝ) + (-h.1.2) := by
        simpa only [NNReal.coe_one, mul_one] using hmajorant (a, 1)
      _ = (-h.1.2) + (-h.1.1) * (a : ℝ) := add_comm _ _
  have hmeanFirst : m < -h.1.1 :=
    ProbabilityBasics.lt_affine_intercept_of_sqrt_asymptotic
      (fun a : ℝ≥0 => g (1, a)) m sigma (-h.1.1) (-h.1.2)
      hsigma hboundary.2 hfirstBound
  -- Coordinate symmetry transfers the same boundary expansion to the other axis.
  have hswap : ∀ a : ℝ≥0, g (a, 1) = g (1, a) := fun a => haxes.1 (1, a)
  have hboundarySwap :
      (fun a : ℝ≥0 => g (a, 1) - (m + 2 * sigma * Real.sqrt (a : ℝ)))
        =o[𝓝[>] (0 : ℝ≥0)] (fun a : ℝ≥0 => Real.sqrt (a : ℝ)) := by
    simpa only [hswap] using hboundary.2
  have hmeanSecond : m < -h.1.2 :=
    ProbabilityBasics.lt_affine_intercept_of_sqrt_asymptotic
      (fun a : ℝ≥0 => g (a, 1)) m sigma (-h.1.2) (-h.1.1)
      hsigma hboundarySwap hsecondBound
  have haxisFirst : g (1, 0) = m := by
    simpa only [NNReal.coe_one, mul_one] using haxes.2.1 1
  have haxisSecond : g (0, 1) = m := by
    simpa only [NNReal.coe_one, mul_one] using haxes.2.2 1
  rw [haxisFirst, haxisSecond]
  exact ⟨hmeanFirst, hmeanSecond⟩

end LPP.Busemann
