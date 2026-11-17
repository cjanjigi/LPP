module

public import LPP_Foundations.Frozen.Model.Environment
public import Busemann.Frozen.Definitions.FiniteEdgeStep
public import Busemann.Frozen.Definitions.OutsideIndex

@[expose] public section

open LPPDifferentiability

namespace LPP.Busemann

/-- The outside weights and cocycle unit increments, in a single array. -/
def outsideWeightsAndCocycleIncrements {Ω : Type*} (weights : Ω → Environment)
    (B : Lattice → Lattice → Ω → ℝ) (V : Finset Lattice) :
    Ω → (OutsideIndex V → ℝ) :=
  fun ω j => match j with
    | .inl x => weights ω x.1
    | .inr (y, i) => B y.1 (y.1 + finiteEdgeStep i) ω

end LPP.Busemann
