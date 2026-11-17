module

public import Busemann.Frozen.StrongExistence.Definitions.PairedSkorokhodPathBorelSpace

@[expose] public section
open MeasureTheory Filter LPPDifferentiability LPP.Busemann
open scoped ENNReal Topology
namespace LPP.Busemann

/-- Read the minus trace at a time in the domain. -/
def evalMinus {S : Set ℝ} {J : Type*} (f : PairedSkorokhodPath S J)
    (t : {u : ℝ // u ∈ S}) : J → ℝ :=
  f.1.1 t

end LPP.Busemann
