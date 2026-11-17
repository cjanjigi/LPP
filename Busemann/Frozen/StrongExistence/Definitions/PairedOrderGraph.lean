module

public import Busemann.Frozen.StrongExistence.Definitions.PairedTraceLE

@[expose] public section
open MeasureTheory Filter LPPDifferentiability LPP.Busemann
open scoped ENNReal Topology
namespace LPP.Busemann

/-- The compact graph of all ordered pairs from a paired path. -/
def pairedOrderGraph {J : Type*} (S : Set ℝ) (f : RawPairedTrace S J) :
    Set (SqueezedState J × SqueezedState J) :=
  {z | z.1 ∈ pairedTraceGraph S f ∧ z.2 ∈ pairedTraceGraph S f ∧
    pairedTraceLE S f z.1 z.2}

end LPP.Busemann
