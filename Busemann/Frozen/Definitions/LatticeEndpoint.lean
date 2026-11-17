-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import LPP_Foundations.Frozen.Model.Lattice

@[expose] public section

open LPPDifferentiability

namespace LPP.Busemann

/-- A nonnegative lattice endpoint read as an integer lattice point. -/
def latticeEndpoint (v : ℕ × ℕ) : Lattice := ((v.1 : ℤ), (v.2 : ℤ))

end LPP.Busemann
