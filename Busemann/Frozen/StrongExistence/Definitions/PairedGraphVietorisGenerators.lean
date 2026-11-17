module

public import Busemann.Frozen.StrongExistence.Definitions.PairedPathOrderGraph

@[expose] public section
open MeasureTheory Filter LPPDifferentiability LPP.Busemann
open scoped ENNReal Topology
namespace LPP.Busemann

/-- The upper and lower Vietoris sets of the actual ordered-pair graphs. -/
def pairedGraphVietorisGenerators (S : Set ℝ) (J : Type*) :
    Set (Set (PairedSkorokhodPath S J)) :=
  {V | ∃ U : Set (SqueezedState J × SqueezedState J), IsOpen U ∧
      V = {f | pairedPathOrderGraph S J f ⊆ U}} ∪
    {V | ∃ U : Set (SqueezedState J × SqueezedState J), IsOpen U ∧
      V = {f | (pairedPathOrderGraph S J f ∩ U).Nonempty}}

end LPP.Busemann
