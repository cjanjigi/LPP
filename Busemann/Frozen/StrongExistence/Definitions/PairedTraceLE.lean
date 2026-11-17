module

public import Busemann.Frozen.StrongExistence.Definitions.PairedTraceGraph

@[expose] public section
open MeasureTheory Filter LPPDifferentiability LPP.Busemann
open scoped ENNReal Topology
namespace LPP.Busemann

/-- Chronological order on the two traces, including their order at an equal time. -/
def pairedTraceLE {J : Type*} (S : Set ℝ) (f : RawPairedTrace S J)
    (p q : SqueezedState J) : Prop :=
  p = q ∨ p = .bottom ∨ q = .top ∨
    (∃ x y : J → ℝ, ∃ t u : ℝ,
      p = .finite x t ∧ q = .finite y u ∧ t < u) ∨
    (∃ t : {u : ℝ // u ∈ S},
      p = .finite (f.1 t) t.val ∧ q = .finite (f.2 t) t.val)

end LPP.Busemann
