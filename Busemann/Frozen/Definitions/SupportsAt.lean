-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import Busemann.Frozen.Definitions.InteriorDirection

@[expose] public section

open LPPDifferentiability

namespace LPP.Busemann

/-- JR arXiv:1810.03580v3, (2.5): the negative tilt is an affine
supergradient of the shape at an interior direction. -/
def SupportsAt (g : Quadrant → ℝ) (ξ : InteriorDirection)
    (h : ℝ × ℝ) : Prop :=
  ∀ z : Quadrant,
    (-h.1) * ((ξ.1.1 : ℝ) - (z.1 : ℝ)) +
      (-h.2) * ((ξ.1.2 : ℝ) - (z.2 : ℝ)) ≤ g ξ.1 - g z

end LPP.Busemann
