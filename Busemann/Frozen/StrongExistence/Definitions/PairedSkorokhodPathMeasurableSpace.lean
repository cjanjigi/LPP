module

public import Busemann.Frozen.StrongExistence.Definitions.PairedSkorokhodPathBorel

@[expose] public section
open MeasureTheory Filter LPPDifferentiability LPP.Busemann
open scoped ENNReal Topology
namespace LPP.Busemann

/-- The measurable structure is the Borel sigma algebra of the generated topology. -/
noncomputable instance (priority := 2000) pairedSkorokhodPathMeasurableSpace
    (S : Set ℝ) (J : Type*) : MeasurableSpace (PairedSkorokhodPath S J) :=
  pairedSkorokhodPathBorel S J

end LPP.Busemann
