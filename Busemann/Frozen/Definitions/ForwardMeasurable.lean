module

public import Busemann.Frozen.Definitions.ForwardWeightSigma

@[expose] public section
open LPPDifferentiability

namespace LPP.Busemann

/-- Every increment with both endpoints northeast of u is measurable from those weights.
Strong Existence, accepted source, lines 470–475. -/
def IsForwardMeasurable (B : Lattice → Lattice → Environment → ℝ) : Prop :=
  ∀ u x y : Lattice, u ≤ x → u ≤ y →
    @Measurable Environment ℝ (forwardWeightSigma u) inferInstance (B x y)

end LPP.Busemann
