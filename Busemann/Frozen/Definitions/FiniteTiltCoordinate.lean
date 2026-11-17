-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import Mathlib.Basic.Real.Basic

@[expose] public section


namespace LPP.Busemann

/-- The corresponding coordinate of a real tilt. -/
def finiteTiltCoordinate (h : ℝ × ℝ) (i : Fin 2) : ℝ :=
  if i.val = 0 then h.1 else h.2

end LPP.Busemann
