module

public import Busemann.Frozen.StrongExistence.Definitions.SqueezedState

@[expose] public section
open MeasureTheory Filter LPPDifferentiability LPP.Busemann
open scoped ENNReal Topology
namespace LPP.Busemann

/-- Compress a time or state coordinate into the open interval `(-1, 1)`. -/
noncomputable def compressReal (a : ℝ) : ℝ := a / (1 + |a|)

end LPP.Busemann
