module

public import Busemann.Frozen.StrongExistence.Definitions.CompressReal

@[expose] public section
open MeasureTheory Filter LPPDifferentiability LPP.Busemann
open scoped ENNReal Topology
namespace LPP.Busemann

/-- The positive scale used to send every state coordinate to zero at a time pole. -/
noncomputable def squeezeScale (t : ℝ) : ℝ := 1 / (1 + |t|)

end LPP.Busemann
