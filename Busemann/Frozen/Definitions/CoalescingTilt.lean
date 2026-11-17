module

public import Busemann.Frozen.Definitions.CoalescingTilts

@[expose] public section
open MeasureTheory LPPDifferentiability

namespace LPP.Busemann

/-- The source tilt index set H, as a subtype of real two-vectors. -/
abbrev CoalescingTilt (μ : Measure ℝ) [IsProbabilityMeasure μ] :=
  {h : ℝ × ℝ // h ∈ coalescingTilts μ}

end LPP.Busemann
