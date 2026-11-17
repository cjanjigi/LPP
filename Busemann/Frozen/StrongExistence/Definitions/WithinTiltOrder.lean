module

public import Busemann.Frozen.StrongExistence.Definitions.MeanTilt

@[expose] public section
open MeasureTheory Filter LPPDifferentiability LPP.Busemann
open scoped ENNReal Topology
namespace LPP.Busemann

/-- At each tilt, order the two branches along each coordinate edge; source lines 638–645, with the author correction. -/
def WithinTiltOrder (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (Bm Bp : StrongField μ) : Prop :=
  ∀ (h : CoalescingTilt μ) (x : Lattice), ∀ᵐ ω ∂environmentLaw μ,
    Bp h x (x + (1, 0)) ω ≤ Bm h x (x + (1, 0)) ω ∧
    Bm h x (x + (0, 1)) ω ≤ Bp h x (x + (0, 1)) ω

end LPP.Busemann
