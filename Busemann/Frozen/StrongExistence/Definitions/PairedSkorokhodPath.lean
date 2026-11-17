module

public import Busemann.Frozen.StrongExistence.Definitions.PairedOrderGraph

@[expose] public section
open MeasureTheory Filter LPPDifferentiability LPP.Busemann
open scoped ENNReal Topology
namespace LPP.Busemann

/-- Paired traces whose chronological order graph is compact. -/
def PairedSkorokhodPath (S : Set ℝ) (J : Type*) :=
  {f : RawPairedTrace S J // IsCompact (pairedOrderGraph S f)}

end LPP.Busemann
