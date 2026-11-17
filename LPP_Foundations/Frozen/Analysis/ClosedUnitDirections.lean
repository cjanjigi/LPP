module

public import LPP_Foundations.Frozen.Model.Quadrant

/-! The closed unit-sum direction segment used in JR1810.03580v3. -/

@[expose] public section

namespace LPPDifferentiability

/-- The closed segment from `(1,0)` to `(0,1)`. Nonnegativity is supplied by
`Quadrant`; unlike `InteriorDirection`, this set retains both endpoints. -/
def closedUnitDirections : Set Quadrant :=
  {ξ | (ξ.1 : ℝ) + (ξ.2 : ℝ) = 1}

end LPPDifferentiability
