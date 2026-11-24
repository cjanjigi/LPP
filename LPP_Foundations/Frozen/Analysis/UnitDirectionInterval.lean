module

public import LPP_Foundations.Frozen.Analysis.ClosedUnitDirections

/-! Closed intervals of unit directions, ordered by the first coordinate. -/

@[expose] public section

namespace LPPDifferentiability

/-- The unit directions whose first coordinates lie in the closed interval `[a,b]`. -/
def unitDirectionInterval (a b : ℝ) : Set Quadrant :=
  {ξ ∈ closedUnitDirections | a ≤ (ξ.1 : ℝ) ∧ (ξ.1 : ℝ) ≤ b}

end LPPDifferentiability
