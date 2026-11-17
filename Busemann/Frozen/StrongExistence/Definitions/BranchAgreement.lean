module

public import Busemann.Frozen.StrongExistence.Definitions.StrongField

@[expose] public section
open MeasureTheory Filter LPPDifferentiability LPP.Busemann
open scoped ENNReal Topology
namespace LPP.Busemann

/-- For each tilt, the two branches agree almost surely at every pair of lattice points; source lines 631–635. -/
def BranchAgreement (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (Bm Bp : StrongField μ) : Prop :=
  ∀ h : CoalescingTilt μ, ∀ᵐ ω ∂environmentLaw μ, ∀ x y, Bm h x y ω = Bp h x y ω

end LPP.Busemann
