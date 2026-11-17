-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import Busemann.Frozen.Definitions.OrderedPair
public import LPP_Foundations.Frozen.Model.LastPassage

@[expose] public section

open LPPDifferentiability

namespace LPP.Busemann

/-- Terminal-excluded passage on its actual ordered-pair carrier. -/
noncomputable def orderedPassage (ω : Environment) (p : OrderedPair) : ℝ :=
  lastPassage ω p.1.1
    ((p.1.2.1 - p.1.1.1).toNat, (p.1.2.2 - p.1.1.2).toNat)

end LPP.Busemann
