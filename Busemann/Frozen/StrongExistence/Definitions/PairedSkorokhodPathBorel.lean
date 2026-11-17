module

public import Busemann.Frozen.StrongExistence.Definitions.PairedSkorokhodPathTopologicalSpace

@[expose] public section
open MeasureTheory Filter LPPDifferentiability LPP.Busemann
open scoped ENNReal Topology
namespace LPP.Busemann

/-- Name the Borel measurable space determined by the generated path topology. -/
@[instance_reducible]
noncomputable def pairedSkorokhodPathBorel (S : Set ℝ) (J : Type*) :
    MeasurableSpace (PairedSkorokhodPath S J) :=
  borel (PairedSkorokhodPath S J)

end LPP.Busemann
