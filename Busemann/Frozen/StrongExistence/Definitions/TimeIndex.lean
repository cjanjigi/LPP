module

public import Busemann.Frozen.StrongExistence.Definitions.TimeSet

@[expose] public section
open MeasureTheory Filter LPPDifferentiability LPP.Busemann
open scoped ENNReal Topology
namespace LPP.Busemann

/-- Index the fixed-domain path by the time associated with a source tilt. -/
def timeIndex (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : CoalescingTilt μ) : {t : ℝ // t ∈ timeSet μ} :=
  ⟨h.val.1 - h.val.2, ⟨h, rfl⟩⟩

end LPP.Busemann
