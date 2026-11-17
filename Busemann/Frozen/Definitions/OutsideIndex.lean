module

public import Busemann.Frozen.Definitions.OutsideLowerOrthants

@[expose] public section

open LPPDifferentiability

namespace LPP.Busemann

/-- Indices for weights outside `V` and unit edges rooted outside its lower orthants. -/
def OutsideIndex (V : Finset Lattice) : Type :=
  Sum {x : Lattice // x ∉ V} ({y : Lattice // y ∈ outsideLowerOrthants V} × Fin 2)

end LPP.Busemann
