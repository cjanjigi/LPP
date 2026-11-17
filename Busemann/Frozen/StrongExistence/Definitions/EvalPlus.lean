module

public import Busemann.Frozen.StrongExistence.Definitions.EvalMinus

@[expose] public section
open MeasureTheory Filter LPPDifferentiability LPP.Busemann
open scoped ENNReal Topology
namespace LPP.Busemann

/-- Read the plus trace at a time in the domain. -/
def evalPlus {S : Set ℝ} {J : Type*} (f : PairedSkorokhodPath S J)
    (t : {u : ℝ // u ∈ S}) : J → ℝ :=
  f.1.2 t

end LPP.Busemann
