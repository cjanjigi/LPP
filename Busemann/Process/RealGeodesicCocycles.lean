/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Geometry.GeodesicPassageDifferenceERealLimit
public import Busemann.Frozen.Definitions.Additive
public import Busemann.Frozen.Definitions.Recovery
public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import LPP_Foundations.Model.LastPassage.PassageDifferenceLimits
public import LPP_Foundations.Model.LastPassage.GeodesicSegments
public import LPP_Foundations.Statements.ShapeDefinitions
import Busemann.Geometry.GeodesicPassageDifferenceLimit
import Busemann.Process.OrdinaryGeodesicDirectedness
import Busemann.Process.AxisGeodesics
import Busemann.Process.NativeBoundaryDenseBarriers
import Busemann.Geometry.EnvironmentUniformPassageBounds
import Busemann.Geometry.StrictSupportFaceSeparation
import Busemann.Geometry.SupportOrder
import LPP_Foundations.Analysis.AbsoluteMomentShape
import LPP_Foundations.Model.LastPassage.GradientOrder
import LPP_Foundations.Model.LastPassage.Outgoing
import LPP_Foundations.Model.LastPassage.Inclusive
import ProbabilityBasics.Probability.ContinuousImageFullEvent
import Martin2004.Shape.ExpectedRateShape
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Busemann.Process.GeodesicNeighborBounds
import Busemann.Geometry.RealGeodesicFields
import Busemann.Geometry.GeodesicCocycleRecovery

@[expose] public section
open MeasureTheory Filter LPPDifferentiability
open scoped ENNReal Topology
namespace LPP.Busemann

/-- Every ordinary maximizing ray escaping in both coordinates generates one
unique finite real cocycle on all signed sites, on one physical measurable
full event. Passage differences determine it at every common valid entry
index; it is additive, recovers the weights and calibrates the actual ray.
Strong Existence, Theorem g400, equations g408a/g408b and
west/south propagation g609, lines 1596–1693. No stationarity or mean statement
is part of this pointwise characterization. -/
theorem exists_full_event_unique_real_geodesic_cocycle
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.NotAPointMass μ)
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞) :
    ∃ A : Set LPPDifferentiability.Environment,
      MeasurableSet A ∧ environmentLaw μ A = 1 ∧
      ∀ ω ∈ A, ∀ u : Lattice, ∀ γ : ℕ → Lattice,
        γ 0 = u →
        (∀ n : ℕ,
          γ (n + 1) = γ n + ((1 : ℤ), (0 : ℤ)) ∨
            γ (n + 1) = γ n + ((0 : ℤ), (1 : ℤ))) →
        has_maximizing_segments ω γ →
        Tendsto (fun n : ℕ => (γ n).1) atTop atTop →
        Tendsto (fun n : ℕ => (γ n).2) atTop atTop →
        ∃! B : Lattice → Lattice → ℝ,
          has_passage_difference_limits ω γ B ∧
          is_additive B ∧ recovers_environment ω B ∧
          ∀ n : ℕ, B (γ n) (γ (n + 1)) = ω (γ n) := by
  classical
  obtain ⟨A, hAmeasurable, hAfull, hGood⟩ :=
    exists_full_event_geodesic_neighbor_increment_upper_bounds μ hμ hmoment
  refine ⟨A, hAmeasurable, hAfull, ?_⟩
  intro ω hω u γ hstart hsteps hsegments hescape₁ hescape₂
  have hsegmentsOld := (has_maximizing_segments_iff ω γ).mp hsegments
  have hNeighborBounds := hGood ω hω u γ hstart hsteps hsegmentsOld hescape₁ hescape₂
  obtain ⟨C, hC, hCUnique⟩ :=
    exists_unique_real_geodesic_pair_field_of_neighbor_bounds
      ω u γ hstart hsteps hsegments hescape₁ hescape₂ hNeighborBounds
  have hRecovery :=
    recovers_environment_and_calibrates_ray_of_passage_difference_limits
      ω u γ C hstart hsteps hsegments hescape₁ hescape₂ hC.1
  refine ⟨C, ?_, ?_⟩
  · exact ⟨hC.1, hC.2, hRecovery.1, hRecovery.2⟩
  · intro C' hC'
    exact hCUnique C' ⟨hC'.1, hC'.2.1⟩

end LPP.Busemann
