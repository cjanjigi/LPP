module

public import Busemann.Frozen.StrongExistence.Definitions.SqueezedStateEmbedding

@[expose] public section
open MeasureTheory Filter LPPDifferentiability LPP.Busemann
open scoped ENNReal Topology
namespace LPP.Busemann

/-- Equip the extended state and time carrier with the topology induced by its embedding. -/
@[instance_reducible]
noncomputable def squeezedStateTopology (J : Type*) : TopologicalSpace (SqueezedState J) :=
  TopologicalSpace.induced (squeezedStateEmbedding J) inferInstance

end LPP.Busemann
