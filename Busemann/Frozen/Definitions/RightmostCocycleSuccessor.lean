module

public import Busemann.StrongExistence.Imports

@[expose] public section
open LPPDifferentiability

namespace LPP.Busemann

/-- Follow a minimal outgoing cocycle increment, taking e1 at a tie.
Strong Existence, accepted source, lines 423–427. -/
noncomputable def rightmostCocycleSuccessor
    (B : Lattice → Lattice → ℝ) (x : Lattice) : Lattice := by
  classical
  exact x + if B x (x + (1, 0)) ≤ B x (x + (0, 1)) then (1, 0) else (0, 1)

end LPP.Busemann
