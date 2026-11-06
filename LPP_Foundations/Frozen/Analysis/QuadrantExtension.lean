module

public import LPP_Foundations.Frozen.Analysis.ToQuadrant

@[expose] public section

namespace LPPDifferentiability

/-- Auxiliary extension for local calculus. Its values outside the quadrant
have no shape interpretation. -/
def quadrantExtension (g : Quadrant → ℝ) (x : ℝ × ℝ) : ℝ := g (toQuadrant x)

end LPPDifferentiability
