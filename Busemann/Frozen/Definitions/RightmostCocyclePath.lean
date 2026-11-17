module

public import Busemann.Frozen.Definitions.RightmostCocycleSuccessor

@[expose] public section
open LPPDifferentiability

namespace LPP.Busemann

/-- The e1-tiebreak path from u at local time n; its absolute level is u.1+u.2+n.
Strong Existence, accepted source, lines 430–438 and 161–166. -/
noncomputable def rightmostCocyclePath
    (B : Lattice → Lattice → ℝ) (u : Lattice) (n : ℕ) : Lattice :=
  (rightmostCocycleSuccessor B)^[n] u

end LPP.Busemann
