-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import LPP_Foundations.Frozen.Model.Lattice

@[expose] public section

open LPPDifferentiability

namespace LPP.Busemann

/-- The horizontal or vertical unit step named by a two-element edge index. -/
def finiteEdgeStep (i : Fin 2) : Lattice :=
  if i.val = 0 then (1, 0) else (0, 1)

end LPP.Busemann
