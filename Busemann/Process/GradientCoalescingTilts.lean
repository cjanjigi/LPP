/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Geometry.SuperdifferentialExtremeEndpoints
public import Busemann.Geometry.ExtremeCoordinateTilts
public import Busemann.Process.NativeExtremeCoalescingTilt
public import LPP_Foundations.Analysis.AbsoluteMomentShape
public import LPP_Foundations.Frozen.Analysis.ClosedUnitDirections
import Busemann.Frozen.Definitions.SupportTilt

@[expose] public section
open Set MeasureTheory LPPDifferentiability
open scoped ENNReal NNReal

namespace LPP.Busemann

/-- Both literal one-sided coordinate-gradient tilts at every interior
direction belong to H under the source's absolute moment assumption.
Strong Existence, first inclusion `eq:Hinc`, lines 582–592. -/
theorem one_sided_coordinate_gradient_tilts_mem_coalescingTilts
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.NotAPointMass μ)
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    (g : Quadrant → ℝ) (hg : IsExpectedRateShape μ g)
    (ξ : InteriorDirection) :
    let a : ℝ := (ξ.1.1 : ℝ)
    let U1 : ℝ → ℝ := fun t => quadrantExtension g (a + t, 1 - a)
    let U2 : ℝ → ℝ := fun t => quadrantExtension g (a, 1 - a + t)
    let hleft : ℝ × ℝ :=
      (-derivWithin U1 (Iio 0) 0, -derivWithin U2 (Ioi 0) 0)
    let hright : ℝ × ℝ :=
      (-derivWithin U1 (Ioi 0) 0, -derivWithin U2 (Iio 0) 0)
    hleft ∈ coalescingTilts μ ∧ hright ∈ coalescingTilts μ := by
  let a : ℝ := (ξ.1.1 : ℝ)
  let U1 : ℝ → ℝ := fun t => quadrantExtension g (a + t, 1 - a)
  let U2 : ℝ → ℝ := fun t => quadrantExtension g (a, 1 - a + t)
  let hleft : ℝ × ℝ :=
    (-derivWithin U1 (Iio 0) 0, -derivWithin U2 (Ioi 0) 0)
  let hright : ℝ × ℝ :=
    (-derivWithin U1 (Ioi 0) 0, -derivWithin U2 (Iio 0) 0)
  change hleft ∈ coalescingTilts μ ∧ hright ∈ coalescingTilts μ

  -- The moment assumption gives the required geometry of the supplied shape.
  have hgeometry :=
    expected_rate_shape_geometry_of_absolute_moment μ g hmoment hg
  have hhom := hgeometry.2.1
  have hconc := hgeometry.2.2

  -- The coordinate theorem gives both literal supports and their
  -- first-coordinate order.
  have hcoordinate :=
    coordinate_extreme_tilts_support_and_order g hconc hhom ξ
  change
    SupportsAt g ξ hleft ∧ SupportsAt g ξ hright ∧
      (∀ k : ℝ × ℝ, SupportsAt g ξ k →
        hleft.1 ≤ k.1 ∧ k.1 ≤ hright.1) at hcoordinate
  rcases hcoordinate with ⟨hleftSupport, hrightSupport, hbounds⟩
  have hleftEndpoint : ∀ k : ℝ × ℝ, SupportsAt g ξ k →
      hleft.1 ≤ k.1 := by
    intro k hk
    exact (hbounds k hk).1
  have hrightEndpoint : ∀ k : ℝ × ℝ, SupportsAt g ξ k →
      k.1 ≤ hright.1 := by
    intro k hk
    exact (hbounds k hk).2

  -- Keep each support attached to the same interior direction.
  let hleftSupportTilt : SupportTilt g :=
    ⟨hleft, ⟨ξ, hleftSupport⟩⟩
  let hrightSupportTilt : SupportTilt g :=
    ⟨hright, ⟨ξ, hrightSupport⟩⟩
  have hξclosed : ξ.1 ∈ closedUnitDirections := by
    change (ξ.1.1 : ℝ) + (ξ.1.2 : ℝ) = 1
    exact ξ.2.2.2

  -- The two support-coordinate endpoints are extreme in the full
  -- superdifferential at the same direction.
  have hleftExtreme :
      -hleftSupportTilt.val ∈
        Set.extremePoints ℝ (quadrantSuperdifferential g ξ.1) :=
    extremePoint_quadrantSuperdifferential_of_support_coordinate_endpoint
      g hhom ξ hleftSupportTilt.val hleftSupport (Or.inl hleftEndpoint)
  have hrightExtreme :
      -hrightSupportTilt.val ∈
        Set.extremePoints ℝ (quadrantSuperdifferential g ξ.1) :=
    extremePoint_quadrantSuperdifferential_of_support_coordinate_endpoint
      g hhom ξ hrightSupportTilt.val hrightSupport (Or.inr hrightEndpoint)

  -- The native producer returns membership in the original-space set H.
  have hleftMem : hleftSupportTilt.val ∈ coalescingTilts μ :=
    extreme_support_tilt_mem_coalescingTilts
      μ hμ hmoment g hg hleftSupportTilt ξ.1 hξclosed hleftExtreme
  have hrightMem : hrightSupportTilt.val ∈ coalescingTilts μ :=
    extreme_support_tilt_mem_coalescingTilts
      μ hμ hmoment g hg hrightSupportTilt ξ.1 hξclosed hrightExtreme
  change
    hleftSupportTilt.val ∈ coalescingTilts μ ∧
      hrightSupportTilt.val ∈ coalescingTilts μ
  exact ⟨hleftMem, hrightMem⟩

end LPP.Busemann
