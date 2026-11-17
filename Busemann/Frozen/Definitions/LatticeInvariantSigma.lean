module

public import LPP_Foundations.Frozen.Model.Environment
public import Mathlib.MeasureTheory.MeasurableSpace.Invariants

@[expose] public section
open LPPDifferentiability

namespace LPP.Busemann

/-- The sigma algebra of measurable events invariant under the full lattice action.
Strong Existence, accepted source, lines 123–128. -/
@[instance_reducible]
def latticeInvariantSigma {Ω : Type*} [m : MeasurableSpace Ω]
    (T : Lattice → Ω → Ω) : MeasurableSpace Ω :=
  ⨅ z : Lattice, @MeasurableSpace.invariants Ω m (T z)

end LPP.Busemann
