module

public import Busemann.Frozen.StrongExistence.Definitions.WithinTiltOrder

@[expose] public section
open MeasureTheory Filter LPPDifferentiability LPP.Busemann
open scoped ENNReal Topology
namespace LPP.Busemann

/-- For strictly increasing first tilt coordinates, compare the adjacent branches along each coordinate edge; source lines 638–645, with the author correction. -/
def StrictCrossTiltOrder (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (Bm Bp : StrongField μ) : Prop :=
  ∀ h h' : CoalescingTilt μ, h.val.1 < h'.val.1 → ∀ x, ∀ᵐ ω ∂environmentLaw μ,
    Bm h' x (x + (1, 0)) ω ≤ Bp h x (x + (1, 0)) ω ∧
    Bp h x (x + (0, 1)) ω ≤ Bm h' x (x + (0, 1)) ω

end LPP.Busemann
