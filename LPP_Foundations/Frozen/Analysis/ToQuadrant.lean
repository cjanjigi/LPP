module

public import LPP_Foundations.Frozen.Model.Quadrant
public import Mathlib.Topology.Instances.NNReal.Lemmas

@[expose] public section

open scoped NNReal

namespace LPPDifferentiability

/-- Retraction used solely to express local calculus at interior points. -/
def toQuadrant (x : ℝ × ℝ) : Quadrant := (x.1.toNNReal, x.2.toNNReal)

end LPPDifferentiability
