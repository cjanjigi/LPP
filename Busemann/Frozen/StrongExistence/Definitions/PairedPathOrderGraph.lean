module

public import Busemann.Frozen.StrongExistence.Definitions.PairedSkorokhodPath

@[expose] public section
open MeasureTheory Filter LPPDifferentiability LPP.Busemann
open scoped ENNReal Topology
namespace LPP.Busemann

/-- The ordered-pair graph of a path in its compact carrier. -/
def pairedPathOrderGraph (S : Set ℝ) (J : Type*)
    (f : PairedSkorokhodPath S J) : Set (SqueezedState J × SqueezedState J) :=
  pairedOrderGraph S f.1

end LPP.Busemann
