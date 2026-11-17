module

public import Busemann.Frozen.StrongExistence.Definitions.RawPairedTrace

@[expose] public section
open MeasureTheory Filter LPPDifferentiability LPP.Busemann
open scoped ENNReal Topology
namespace LPP.Busemann

/-- The two poles and both finite traces of a paired path. -/
def pairedTraceGraph {J : Type*} (S : Set ℝ) (f : RawPairedTrace S J) :
    Set (SqueezedState J) :=
  {p | p = .bottom ∨ p = .top ∨
    ∃ t : {u : ℝ // u ∈ S},
      p = .finite (f.1 t) t.val ∨ p = .finite (f.2 t) t.val}

end LPP.Busemann
