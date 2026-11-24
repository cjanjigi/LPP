/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.Frozen.FinalDraft.SiteSurvival
public import Differentiability.Model.OrientedPercolation
public import LPP_Foundations.Frozen.Model.EnvironmentLaw

/-! Asymptotic right-edge speed of the origin cluster on survival. -/

@[expose] public section

open Filter MeasureTheory
open scoped Topology

namespace LPPDifferentiability.FinalDraft

/-- On survival, the first coordinate of the origin cluster's rightmost
site, divided by its level, converges almost surely to `β`. -/
def IsOriginRightEdgeSpeed (μ : Measure ℝ) [IsProbabilityMeasure μ] (M β : ℝ) : Prop :=
  ∀ᵐ ω ∂environmentLaw μ, ω ∈ orientedSiteSurvival M →
    Tendsto
      (fun n : ℕ =>
        (openEdge {z | ω z = M} ({0} : Set Lattice) (n + 1) : ℝ) / ((n : ℝ) + 1))
      atTop (𝓝 β)

end LPPDifferentiability.FinalDraft
