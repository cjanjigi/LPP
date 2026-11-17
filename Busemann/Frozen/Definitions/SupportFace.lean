-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import Busemann.Frozen.Definitions.SupportTilt

@[expose] public section

open LPPDifferentiability

namespace LPP.Busemann

/-- The interior contact face of one support tilt. -/
def supportFace (g : Quadrant → ℝ) (h : SupportTilt g) :
    Set InteriorDirection :=
  {η | SupportsAt g η h.1}

end LPP.Busemann
