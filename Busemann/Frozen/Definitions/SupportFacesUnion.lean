-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import Busemann.Frozen.Definitions.SupportFace

@[expose] public section

open LPPDifferentiability

namespace LPP.Busemann

/-- The union of two support faces; for the extreme pair at ξ this is U_ξ. -/
def supportFacesUnion (g : Quadrant → ℝ)
    (hMinus hPlus : SupportTilt g) : Set InteriorDirection :=
  supportFace g hMinus ∪ supportFace g hPlus

end LPP.Busemann
