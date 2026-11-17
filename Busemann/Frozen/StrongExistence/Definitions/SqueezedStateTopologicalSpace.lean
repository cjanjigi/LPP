module

public import Busemann.Frozen.StrongExistence.Definitions.SqueezedStateTopology

@[expose] public section
open MeasureTheory Filter LPPDifferentiability LPP.Busemann
open scoped ENNReal Topology
namespace LPP.Busemann

noncomputable instance (priority := 2000) squeezedStateTopologicalSpace (J : Type*) :
    TopologicalSpace (SqueezedState J) := squeezedStateTopology J

end LPP.Busemann
