-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import LPP_Foundations.Frozen.Model.Lattice

@[expose] public section

open LPPDifferentiability

namespace LPP.Busemann

/-- The pairs (x,y) that are valid for terminal-excluded last-passage time. -/
abbrev OrderedPair := {p : Lattice × Lattice // p.1 ≤ p.2}

end LPP.Busemann
