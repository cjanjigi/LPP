-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import LPP_Foundations.Frozen.Model.Quadrant

@[expose] public section

open LPPDifferentiability

namespace LPP.Busemann

/-- A direction in the relative interior of the unit-sum segment. -/
abbrev InteriorDirection :=
  {ξ : Quadrant // 0 < ξ.1 ∧ 0 < ξ.2 ∧
    (ξ.1 : ℝ) + (ξ.2 : ℝ) = 1}

end LPP.Busemann
