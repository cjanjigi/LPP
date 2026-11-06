module

public import Mathlib.Topology.Instances.NNReal.Lemmas

@[expose] public section

open scoped NNReal

namespace LPPDifferentiability

/-- The closed positive quadrant, the actual domain of the shape. -/
abbrev Quadrant := ℝ≥0 × ℝ≥0

end LPPDifferentiability
