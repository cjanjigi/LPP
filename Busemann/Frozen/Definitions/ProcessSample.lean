-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import LPP_Foundations.Frozen.Model.Environment

@[expose] public section

open LPPDifferentiability

namespace LPP.Busemann

/-- One canonical environment together with a countable array of two outgoing edge values. -/
abbrev ProcessSample := Environment × (ℕ → Lattice → Fin 2 → ℝ)

end LPP.Busemann
