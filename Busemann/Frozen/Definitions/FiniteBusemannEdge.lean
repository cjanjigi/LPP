-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import Busemann.Frozen.Definitions.FiniteTiltedPotential
public import Busemann.Frozen.Definitions.FiniteEdgeStep
public import Busemann.Frozen.Definitions.FiniteTiltCoordinate

@[expose] public section

open LPPDifferentiability

namespace LPP.Busemann

/-- The finite Busemann edge value; the inactive source boundary value is zero. -/
noncomputable def finiteBusemannEdge (ω : Environment) (h : ℝ × ℝ)
    (x : Lattice) (n : ℤ) (i : Fin 2) : ℝ := by
  classical
  by_cases hx : x.1 + x.2 < n
  · have hx1 : (x + finiteEdgeStep i).1 + (x + finiteEdgeStep i).2 ≤ n := by
      simp [finiteEdgeStep]
      split_ifs <;> simp <;> omega
    exact (finiteTiltedPotential ω h x n).toReal -
      (finiteTiltedPotential ω h (x + finiteEdgeStep i) n).toReal -
      finiteTiltCoordinate h i
  · exact 0

end LPP.Busemann
