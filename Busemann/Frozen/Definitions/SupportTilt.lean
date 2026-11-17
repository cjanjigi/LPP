-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import Busemann.Frozen.Definitions.SupportsAt

@[expose] public section

open LPPDifferentiability

namespace LPP.Busemann

/-- JR's support-tilt domain H: negative supports with some interior contact. -/
abbrev SupportTilt (g : Quadrant → ℝ) :=
  {h : ℝ × ℝ // ∃ ξ : InteriorDirection, SupportsAt g ξ h}

end LPP.Busemann
