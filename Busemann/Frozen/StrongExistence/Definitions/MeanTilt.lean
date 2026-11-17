module

public import Busemann.Frozen.StrongExistence.Definitions.ForwardCoalescingClass

@[expose] public section
open MeasureTheory Filter LPPDifferentiability LPP.Busemann
open scoped ENNReal Topology
namespace LPP.Busemann

/-- The two origin edge means equal the negatives of the corresponding tilt coordinates; source line 637. -/
def MeanTilt (μ : Measure ℝ) [IsProbabilityMeasure μ] (Bm : StrongField μ) : Prop :=
  ∀ h : CoalescingTilt μ, (∫ ω, Bm h 0 (1, 0) ω ∂environmentLaw μ) = -h.val.1 ∧
    (∫ ω, Bm h 0 (0, 1) ω ∂environmentLaw μ) = -h.val.2

end LPP.Busemann
