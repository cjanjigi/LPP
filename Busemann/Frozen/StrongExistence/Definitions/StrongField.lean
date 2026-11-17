module

public import Busemann.Frozen.Definitions.ForwardMeasurable

@[expose] public section
open MeasureTheory Filter LPPDifferentiability LPP.Busemann
open scoped ENNReal Topology
namespace LPP.Busemann

/-- The full two-branch process field indexed by the source tilt set. -/
abbrev StrongField (μ : Measure ℝ) [IsProbabilityMeasure μ] :=
  CoalescingTilt μ → Lattice → Lattice → Environment → ℝ

end LPP.Busemann
