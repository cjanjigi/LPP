module

public import Busemann.Frozen.StrongExistence.Definitions.PairedSkorokhodPathMeasurableSpace

@[expose] public section
open MeasureTheory Filter LPPDifferentiability LPP.Busemann
open scoped ENNReal Topology
namespace LPP.Busemann

/-- This measurable structure is Borel for the actual topology on paired paths. -/
instance (priority := 2000) pairedSkorokhodPathBorelSpace
    (S : Set ℝ) (J : Type*) : BorelSpace (PairedSkorokhodPath S J) := ⟨rfl⟩

end LPP.Busemann
