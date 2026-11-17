-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import Busemann.Frozen.Definitions.ProcessSample

@[expose] public section

open LPPDifferentiability

namespace LPP.Busemann

/-- The weights outside every northeast cone rooted in I. -/
def pastVariables (I : Set Lattice) (s : ProcessSample) :
    {x : Lattice // ∀ z ∈ I, ¬ z ≤ x} → ℝ :=
  fun x => s.1 x.1

end LPP.Busemann
