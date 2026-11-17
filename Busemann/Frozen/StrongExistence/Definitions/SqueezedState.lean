module

public import Busemann.Frozen.StrongExistence.Definitions.OneSidedLimits

@[expose] public section
open MeasureTheory Filter LPPDifferentiability LPP.Busemann
open scoped ENNReal Topology
namespace LPP.Busemann

/-- The compressed state space has finite states and two time poles. -/
inductive SqueezedState (J : Type*) where
  | finite (state : J → ℝ) (time : ℝ)
  | bottom
  | top

end LPP.Busemann
