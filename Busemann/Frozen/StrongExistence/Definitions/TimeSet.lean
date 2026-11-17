module

public import Busemann.Frozen.StrongExistence.Definitions.EvalPlus

@[expose] public section
open MeasureTheory Filter LPPDifferentiability LPP.Busemann
open scoped ENNReal Topology
namespace LPP.Busemann

/-- The times obtained by subtracting the second tilt coordinate from the first on H. -/
def timeSet (μ : Measure ℝ) [IsProbabilityMeasure μ] : Set ℝ :=
  {t | ∃ h : CoalescingTilt μ, t = h.val.1 - h.val.2}

end LPP.Busemann
