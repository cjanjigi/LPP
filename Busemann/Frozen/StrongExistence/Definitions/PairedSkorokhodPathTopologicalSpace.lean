module

public import Busemann.Frozen.StrongExistence.Definitions.PairedSkorokhodPathTopology

@[expose] public section
open MeasureTheory Filter LPPDifferentiability LPP.Busemann
open scoped ENNReal Topology
namespace LPP.Busemann

instance (priority := 2000) pairedSkorokhodPathTopologicalSpace
    (S : Set ℝ) (J : Type*) : TopologicalSpace (PairedSkorokhodPath S J) :=
  pairedSkorokhodPathTopology S J

end LPP.Busemann
