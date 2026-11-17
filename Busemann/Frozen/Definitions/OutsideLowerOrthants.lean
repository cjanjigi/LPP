module

public import LPP_Foundations.Frozen.Model.Lattice
public import Mathlib.Data.Finset.Basic

@[expose] public section

open LPPDifferentiability

namespace LPP.Busemann

/-- Sites outside every lower orthant rooted at a site of `V`. -/
def outsideLowerOrthants (V : Finset Lattice) : Set Lattice :=
  {y | ∀ x ∈ V, ¬ y ≤ x}

end LPP.Busemann
