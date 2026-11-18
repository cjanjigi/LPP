/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Process.MonotoneCocycleLimit
public import Busemann.Frozen.Definitions.CoalescingTilt
public import Busemann.Geometry.CocycleSoutheastOrder
public import LPP_Foundations.Statements.WeightMoments

import Busemann.Process.CoalescingRayGlobalOrder
import Busemann.Process.CoalescingRayCocycleOrder
import Busemann.Probability.CanonicalCocycleMeans

/-! Strict ordering of canonical forward coalescing cocycles gives opposite
ordering of their signed edge values, following the published monotonicity
proof in Strong Existence, lines 1155–1166. -/

@[expose] public section

open MeasureTheory Filter LPPDifferentiability
open scoped ENNReal Topology

namespace LPP.Busemann

-- The named parameters `hForwardC`, `hForwardB`, `hmoment`, `hμ` are part of the shared theorem interface.
set_option linter.unusedVariables false in
/-- Opposite edge order for two canonical forward coalescing witnesses whose
deterministic tilts are ordered by their first coordinate. -/
theorem ae_forward_coalescing_cocycle_opposite_edge_order
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.NotAPointMass μ)
    (hmoment : LPPStatements.HasAbsoluteMomentAbove μ 2)
    (B C : Lattice → Lattice → Environment → ℝ)
    (hB : IsGeneralizedBusemann (environmentLaw μ)
      (fun z ω => environmentTranslationEquiv z ω) (fun ω => ω) B)
    (hC : IsGeneralizedBusemann (environmentLaw μ)
      (fun z ω => environmentTranslationEquiv z ω) (fun ω => ω) C)
    (hForwardB : IsForwardMeasurable B)
    (hForwardC : IsForwardMeasurable C)
    (hCoalB : HasCoalescingRightmostPaths (environmentLaw μ) B)
    (hCoalC : HasCoalescingRightmostPaths (environmentLaw μ) C)
    (h k : ℝ × ℝ)
    (hTiltB : ∀ᵐ ω ∂environmentLaw μ,
      invariantCocycleTilt (environmentLaw μ)
        (fun z ω => environmentTranslationEquiv z ω) (fun ω => ω) B hB ω = h)
    (hTiltC : ∀ᵐ ω ∂environmentLaw μ,
      invariantCocycleTilt (environmentLaw μ)
        (fun z ω => environmentTranslationEquiv z ω) (fun ω => ω) C hC ω = k)
    (hfirst : h.1 < k.1) :
    ∀ᵐ ω ∂environmentLaw μ,
      cocycleSoutheastLE (fun x y => B x y ω) (fun x y => C x y ω) := by
  rcases ae_rightmostCocyclePaths_globally_comparable
      μ B C hB hC hCoalB hCoalC with hPathsBC | hPathsCB
  · exact ae_cocycle_opposite_edge_order_of_rightmostPath_order
      μ B C hB hC hCoalB hCoalC hPathsBC
  · have hEdgesCB := ae_cocycle_opposite_edge_order_of_rightmostPath_order
      μ C B hC hB hCoalC hCoalB hPathsCB
    have hEast : ∀ᵐ ω ∂environmentLaw μ,
        B 0 ((1 : ℤ), (0 : ℤ)) ω ≤ C 0 ((1 : ℤ), (0 : ℤ)) ω := by
      filter_upwards [hEdgesCB] with ω hω
      simpa only [zero_add] using (hω 0).1
    have hEastMeans := canonical_origin_means_of_deterministic_invariant_tilt
      μ B hB h hTiltB
    have hEastMeansC := canonical_origin_means_of_deterministic_invariant_tilt
      μ C hC k hTiltC
    have hEastIntegral :
        (∫ ω, B 0 ((1 : ℤ), (0 : ℤ)) ω ∂environmentLaw μ) ≤
          ∫ ω, C 0 ((1 : ℤ), (0 : ℤ)) ω ∂environmentLaw μ := by
      exact integral_mono_ae (hB.2.2 0 ((1 : ℤ), (0 : ℤ)))
        (hC.2.2 0 ((1 : ℤ), (0 : ℤ))) hEast
    have hTiltOrder : -h.1 ≤ -k.1 := by
      simpa only [hEastMeans.1, hEastMeansC.1] using hEastIntegral
    linarith

end LPP.Busemann
